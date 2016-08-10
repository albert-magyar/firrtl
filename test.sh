#!/bin/bash
sbt "run-main firrtl.Driver -i bmem.fir -o bmem.v -X verilog --noInlineMem Top"
