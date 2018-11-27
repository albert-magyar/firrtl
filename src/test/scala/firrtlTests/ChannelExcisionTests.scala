// See LICENSE for license details.

package firrtlTests

import org.scalatest.FlatSpec
import org.scalatest.Matchers
import org.scalatest.junit.JUnitRunner
import firrtl.{LowForm, SeqTransform}
import firrtl.ir.Circuit
import firrtl.Parser
import firrtl.passes.PassExceptions
import firrtl.annotations.{Annotation, InstanceTarget, CircuitTarget}
import firrtl.transforms.fame._
import logger.{LogLevel, Logger}
import logger.LogLevel.Debug


/**
  * Tests deep inline transformation
  */
class ExciseWireChannelTests extends LowTransformSpec {
  def transform = new firrtl.SeqTransform {
    def inputForm = LowForm
    def outputForm = LowForm
    def transforms = Seq(new FAMEDefaults, new ChannelExcision)
  }

  "Wire channels" should "replaced with source and sink ports on the IO of Top" in {
    val input =
      """circuit Top :
        |  module Top :
        |    input hostReset : UInt<1>
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst a of Model
        |    inst b of Model
        |    a.i <= i
        |    b.i <= a.o
        |    o <= b.o
        |  module Model :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    val iAnnos = Seq(FAMEHostReset(CircuitTarget("Top").module("Top").ref("hostReset")),
                     FAMEModelAnnotation(CircuitTarget("Top").module("Top").instOf("a", "Model")),
                     FAMEModelAnnotation(CircuitTarget("Top").module("Top").instOf("b", "Model")))
    val check =
      """circuit Top :
        |  module Top :
        |    input hostReset : UInt<1>
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    output a_o_source : UInt<32>
        |    input b_i_sink : UInt<32>
        |    inst a of Model
        |    inst b of Model
        |    o <= b.o
        |    a.i <= i
        |    b.i <= b_i_sink
        |    a_o_source <= a.o
        |  module Model :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin

    val checkAnnos = Seq(FAMEChannelAnnotation("a_o__to__b_i", WireChannel,
                         Some(Seq(CircuitTarget("Top").module("Top").ref("a_o_source"))),
                         Some(Seq(CircuitTarget("Top").module("Top").ref("b_i_sink")))))

    val outputState = execute(input, check, iAnnos)
    checkAnnos.foreach({ anno =>
      (outputState.annotations.toSeq) should contain (anno)
    })
  }
}
