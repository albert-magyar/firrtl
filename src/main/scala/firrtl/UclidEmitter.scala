// See LICENSE for license details.

package firrtl

import com.typesafe.scalalogging.LazyLogging
import java.nio.file.{Paths, Files}
import java.io.{Reader, Writer}

import scala.collection.mutable
import scala.sys.process._
import scala.io.Source

import firrtl.ir._
import firrtl.passes._
import firrtl.transforms._
import firrtl.annotations._
import firrtl.Mappers._
import firrtl.PrimOps._
import firrtl.WrappedExpression._
import Utils._
import MemPortUtils.{memPortField, memType}
// Datastructures
import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashSet}

class IndentLevel {
  var value: Int = 0
  def increase() = value += 2
  def decrease() = value -= 2
}

class UclidEmitter extends SeqTransform with Emitter {
  def inputForm = LowForm
  def outputForm = LowForm

  private def serialize_rhs_ref(wr: WRef)(implicit rhsPrimes: Boolean): String = {
    if (rhsPrimes) s"${wr.name}'" else s"${wr.name}"
  }

  private def serialize_unop(p: DoPrim, arg0: String): String = p.op match {
    case Neg => s"-$arg0"
    // TODO: fix big hack that assumes all 1-bit UInts are booleans
    case Not => if (get_width(p.tpe) == 1) s"!${arg0}" else s"~$arg0"
    case _ => throwInternalError(s"Illegal unary operator: ${p.op}")
  }

  private def serialize_binop(p: DoPrim, arg0: String, arg1: String): String = p.op match {
    case Add => s"(0bv1 ++ $arg0) + (0bv1 ++ $arg1)"
    case Sub => s"(0bv1 ++ $arg0) - (0bv1 ++ $arg1)"
    case Lt => s"$arg0 < $arg1"
    case Leq => s"$arg0 <= $arg1"
    case Gt => s"$arg0 > $arg1"
    case Geq => s"$arg0 >= $arg1"
    case Eq => s"$arg0 == $arg1"
    case Neq => s"$arg0 != $arg1"
    case And =>
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      if (get_width(p.tpe) == 1)
        s"$arg0 && $arg1"
      else
        s"$arg0 & $arg1"
    case Or =>
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      if (get_width(p.tpe) == 1)
        s"$arg0 || $arg1"
      else
        s"$arg0 | $arg1"
    case Xor => s"$arg0 ^ $arg1"
    case Bits => s"${arg0}[${arg1}]"
    case Cat => s"${arg0} ++ ${arg1}"
    case Pad =>
      val extra_bits = p.consts(0) - get_width(p.args(0).tpe)
      if (extra_bits > 0) 
        s"0bv${extra_bits} ++ ${arg0}"
      else
        s"${arg0}"
    case _ => throwInternalError(s"Illegal binary operator: ${p.op}")
  }

  private def serialize_ternop(p: DoPrim, arg0: String, arg1: String, arg2: String): String = p.op match {
    case Bits => s"${arg0}[${arg1}:${arg2}]"
    case _ => throwInternalError(s"Illegal ternary operator: ${p.op}")
  }

  private def serialize_prim(p: DoPrim)(implicit rhsPrimes: Boolean): String = (p.args.length, p.consts.length) match {
    case (2, 0) => serialize_binop(p, serialize_rhs_exp(p.args(0)), serialize_rhs_exp(p.args(1)))
    case (1, 0) => serialize_unop(p, serialize_rhs_exp(p.args(0)))
    case (1, 2) => serialize_ternop(p, serialize_rhs_exp(p.args(0)), p.consts(0).toString, p.consts(1).toString)
    case (1, 1) => serialize_binop(p, serialize_rhs_exp(p.args(0)), p.consts(0).toString)
    case (0, 2) => serialize_binop(p, p.consts(0).toString, p.consts(1).toString)
    case (0, 1) => serialize_unop(p, p.consts(0).toString)
    case _ => throwInternalError(s"Illegal primitive operator operands")
  }

  private def serialize_mux(m: Mux)(implicit rhsPrimes: Boolean): String = {
    val i = serialize_rhs_exp(m.cond)
    val t = serialize_rhs_exp(m.tval)
    val e = serialize_rhs_exp(m.fval)
    s"if ($i) then ($t) else ($e)"
  }

  private def get_width(w: Width): Int = w match {
    case IntWidth(iw: BigInt) => iw.intValue
    case _ => throwInternalError(s"Types must have integral widths")
  }

  private def get_width(tpe: Type): Int = tpe match {
    case UIntType(w: Width) => get_width(w)
    case SIntType(w: Width) => get_width(w)
    case _ => throwInternalError(s"Cannot get width of type ${tpe}")
  }

  private def serialize_rhs_exp(e: Expression)(implicit rhsPrimes: Boolean): String = e match {
    case wr: WRef => serialize_rhs_ref(wr)
    case m: Mux => serialize_mux(m)
    case p: DoPrim => serialize_prim(p)
    case ul: UIntLiteral => get_width(ul.width) match {
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      case 1 => if (ul.value == 1) "true" else "false"
      case i: Int =>
        s"${ul.value}bv${i}"
    }
    case _ => throwInternalError(s"Trying to emit unsupported expression")
  }

  private def serialize_lhs_exp(e: Expression): String = e match {
    case wr: WRef => wr.name
    case _ => throwInternalError(s"Trying to emit unsupported expression")
  }

  private def serialize_type(tpe: Type): String = tpe match {
    case UIntType(w: Width) => get_width(w) match {
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      case 1 => "boolean"
      case i: Int => s"bv${i}"
    }
    case SIntType(w: Width) => s"bv${get_width(w)}"
    case _ => throwInternalError(s"Trying to emit unsupported type")
  }

  private def indent_line()(implicit w: Writer, indent: IndentLevel): Unit = {
    w write (" " * indent.value)
  }

  private def emit_comment(s: String)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line();
    w write s"// ${s}\n"
  }

  private def emit_port(p: Port)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val dir = if (p.direction == Input) "input" else "output"
    val uclType = serialize_type(p.tpe)
    w write s"${dir} ${p.name} : ${uclType};\n"
  }

  private def emit_reg_decl(r: DefRegister)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(r.tpe)
    w write s"var ${r.name} : ${uclType};\n"
  }

  private def emit_node_decl(r: DefNode)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(r.value.tpe)
    w write s"var ${r.name} : ${uclType};\n"
  }

  private def emit_node_assignment(n: DefNode)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    indent_line()
    w write s"${n.name}' = "
    w write serialize_rhs_exp(n.value)
    w write ";\n"
  }

  private def emit_connect(c: Connect)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    val lhs = serialize_lhs_exp(c.loc)
    indent_line()
    w write s"${lhs}' = "
    w write serialize_rhs_exp(c.expr)
    w write ";\n"
  }

  private def emit_open_module_scope(m: Module)(implicit w: Writer, indent: IndentLevel): Unit = {
    w write s"module ${m.name} {\n"
    indent.increase()
  }

  private def emit_open_next_scope()(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    w write s"next {\n"
    indent.increase()
  }

  private def emit_close_scope()(implicit w: Writer, indent: IndentLevel): Unit = {
    indent.decrease()
    indent_line()
    w write s"}\n"
  }

  private def emit_module(m: Module)(implicit w: Writer): Unit = {
    // Just IO, nodes, registers
    val nodes = ArrayBuffer[DefNode]()
    val output_decls = m.ports.filter(_.direction == Output).map(p => p.name -> p).toMap
    val reg_clocks = HashSet[Expression]()
    val reg_resets = HashSet[String]()
    val reg_decls = LinkedHashMap[String, DefRegister]()
    val reg_assigns = ArrayBuffer[Connect]()
    val output_assigns = ArrayBuffer[Connect]()
    def processStatements(s: Statement): Statement = s map processStatements match {
      case sx: DefNode =>
        nodes += sx
        sx
      case sx: DefRegister =>
        reg_clocks += sx.clock
        sx.reset match {
          case wr: WRef =>
            reg_resets += wr.name
          case UIntLiteral(v: BigInt, _) if (v == 0) =>
          case _ => throwInternalError(s"Illegal reset signal ${sx.reset}")
        }
        reg_decls += sx.name -> sx
        sx
      case sx @ Connect(_, wr: WRef, _) =>
        if (reg_decls.contains(wr.name)) {
          reg_assigns += sx
        } else if (output_decls.contains(wr.name)) {
          output_assigns += sx
        } else {
          throwInternalError(s"Only outputs and Registers may be the lhs of Connect")
        }
        sx
      case sx: DefMemory =>
        // Unimplemented
        throw EmitterException("Firrtl memories are unsupported when emitting UCLID!")
      case Connect(_,_,_) | DefWire(_,_,_) | WDefInstance(_,_,_,_) =>
        // These are illegal for now
        throw EmitterException("Using illegal statement!")
      case sx =>
        sx
    }
    processStatements(m.body)
    // Consistency checks to see if module uses <=1 clock and <=1 reset
    if (reg_clocks.size > 1 || reg_resets.size > 0)
      throw EmitterException("Uclid backend supports only a single clock and zero explicit resets")
    implicit val indent = new IndentLevel()
    emit_open_module_scope(m)
    m.ports.filter(p => p.tpe != ClockType && !reg_resets.contains(p.name)).foreach(emit_port(_))
    emit_comment("Registers")
    reg_decls.foreach({ case (k, v) => emit_reg_decl(v) })
    emit_comment("Nodes")
    nodes.foreach(emit_node_decl(_))
    emit_open_next_scope()
    implicit var rhsPrimes = false
    reg_assigns.foreach(emit_connect(_))
    rhsPrimes = true
    nodes.foreach(emit_node_assignment(_))
    output_assigns.foreach(emit_connect(_))
    emit_close_scope()
    emit_close_scope()
  }

  def emit(cs: CircuitState, w: Writer): Unit = {
    val circuit = runTransforms(cs).circuit
    assert(circuit.modules.length == 1) // flat circuits, for now
    circuit.modules.head match {
      case m: Module => emit_module(m)(w)
      case _ => throw EmitterException(s"UCLID backed supports ordinary modules only!")
    }
  }

  /** Transforms to run before emission */
  def transforms = Seq(
    new RemoveTail
  )

  override def execute(cs: CircuitState): CircuitState = {
    val extraAnnotations = cs.annotations.flatMap {
      case EmitCircuitAnnotation(_) =>
        val writer = new java.io.StringWriter
        emit(cs, writer)
        Seq(EmittedVerilogCircuitAnnotation(EmittedVerilogCircuit(cs.circuit.main, writer.toString)))
      case _ => Seq()
    }
    cs.copy(annotations = extraAnnotations ++ cs.annotations)
  }
}
