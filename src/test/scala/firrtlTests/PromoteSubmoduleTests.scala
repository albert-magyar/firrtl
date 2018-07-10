// See LICENSE for license details.

package firrtlTests

import org.scalatest.FlatSpec
import org.scalatest.Matchers
import org.scalatest.junit.JUnitRunner
import firrtl.ir.Circuit
import firrtl.Parser
import firrtl.passes.PassExceptions
import firrtl.annotations.{Annotation, CircuitName, ComponentName, ModuleName, Named}
import firrtl.transforms.{PromoteSubmoduleAnnotation, PromoteSubmodule}
import logger.{LogLevel, Logger}
import logger.LogLevel.Debug


/**
  * Tests deep inline transformation
  */
class PromoteSubmoduleTests extends HighTransformSpec {
  def transform = new PromoteSubmodule
  def promote(mod: String): Annotation = {
    val parts = mod.split('.')
    val modName = ModuleName(parts.head, CircuitName("Top")) // If this fails, bad input
    val name = if (parts.size == 1) modName else ComponentName(parts.tail.mkString("."), modName)
    PromoteSubmoduleAnnotation(name)
  }

  "The instance c in Parent" should "be promoted" in {
    val input =
      """circuit Top :
        |  module Top :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst p of Parent
        |    p.i <= i
        |    o <= p.o
        |  module Parent :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst c of Child
        |    c.i <= i
        |    o <= c.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    val check =
      """circuit Top :
        |  module Top :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst p of Parent
        |    inst p_c of Child
        |    p.c <= p_c
        |    p.i <= i
        |    o <= p.o
        |  module Parent :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    input c : { flip i : UInt<32>, o : UInt<32> }
        |    c.i <= i
        |    o <= c.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    execute(input, check, Seq(promote("Parent.c")))
  }

  "The instances c1 and c2 in Parent" should "be promoted" in {
    val input =
      """circuit Top :
        |  module Top :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    inst p of Parent
        |    p.i1 <= i1
        |    o1 <= p.o1
        |    p.i2 <= i2
        |    o2 <= p.o2
        |  module Parent :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    inst c1 of Child
        |    c1.i <= i1
        |    o1 <= c1.o
        |    inst c2 of Child
        |    c2.i <= i2
        |    o2 <= c2.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    val check =
      """circuit Top :
        |  module Top :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    inst p of Parent
        |    inst p_c1 of Child
        |    p.c1 <= p_c1
        |    inst p_c2 of Child
        |    p.c2 <= p_c2
        |    p.i1 <= i1
        |    o1 <= p.o1
        |    p.i2 <= i2
        |    o2 <= p.o2
        |  module Parent :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    input c2 : { flip i : UInt<32>, o : UInt<32> }
        |    input c1 : { flip i : UInt<32>, o : UInt<32> }
        |    c1.i <= i1
        |    o1 <= c1.o
        |    c2.i <= i2
        |    o2 <= c2.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    execute(input, check, Seq(promote("Parent.c1"), promote("Parent.c2")))
  }

  "Each instance of c from multiple parent instances" should "be promoted" in {
    val input =
      """circuit Top :
        |  module Top :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    inst p1 of Parent
        |    inst p2 of Parent
        |    p1.i <= i1
        |    o1 <= p1.o
        |    p2.i <= i2
        |    o2 <= p2.o
        |  module Parent :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst c of Child
        |    c.i <= i
        |    o <= c.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin

    val check =
      """circuit Top :
        |  module Top :
        |    input i1 : UInt<32>
        |    output o1 : UInt<32>
        |    input i2 : UInt<32>
        |    output o2 : UInt<32>
        |    inst p1 of Parent
        |    inst p1_c of Child
        |    p1.c <= p1_c
        |    inst p2 of Parent
        |    inst p2_c of Child
        |    p2.c <= p2_c
        |    p1.i <= i1
        |    o1 <= p1.o
        |    p2.i <= i2
        |    o2 <= p2.o
        |  module Parent :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    input c : { flip i : UInt<32>, o : UInt<32> }
        |    c.i <= i
        |    o <= c.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    execute(input, check, Seq(promote("Parent.c")))
  }
}
