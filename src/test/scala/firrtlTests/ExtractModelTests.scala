// See LICENSE for license details.

package firrtlTests

import org.scalatest.FlatSpec
import org.scalatest.Matchers
import org.scalatest.junit.JUnitRunner
import firrtl.ir.Circuit
import firrtl.Parser
import firrtl.passes.PassExceptions
import firrtl.annotations.{Annotation, InstanceTarget, CircuitTarget}
import firrtl.transforms.fame.{FAMEModelAnnotation, ExtractModel}
import logger.{LogLevel, Logger}
import logger.LogLevel.Debug


/**
  * Tests deep inline transformation
  */
class ExtractModelTests extends HighTransformSpec {
  def transform = new ExtractModel

  "The annotated instance" should "be promoted to a child of Top" in {
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
        |    inst gc of Grandchild
        |    gc.i <= i
        |    o <= gc.o
        |  module Grandchild :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    val check =
      """circuit Top :
        |  module Top :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    inst p of Parent
        |    inst p_c_gc of Grandchild
        |    p.c_gc <= p_c_gc
        |    p.i <= i
        |    o <= p.o
        |  module Parent :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    input c_gc : { flip i : UInt<32>, o : UInt<32> }
        |    inst c of Child
        |    c.gc <= c_gc
        |    c.i <= i
        |    o <= c.o
        |  module Child :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    input gc : { flip i : UInt<32>, o : UInt<32> }
        |    gc.i <= i
        |    o <= gc.o
        |  module Grandchild :
        |    input i : UInt<32>
        |    output o : UInt<32>
        |    o <= i""".stripMargin
    execute(input, check, Seq(FAMEModelAnnotation(CircuitTarget("Top").module("Child").instOf("gc", "Grandchild"))))
  }
}
