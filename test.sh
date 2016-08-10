#!/bin/bash
sbt "run-main firrtl.Driver -i bmem.fir -o bmem.fir.out -X verilog --noInlineMem Top"
