circuit Top : 
  module Top : 
    input clk : Clock
    wire i : UInt<5>
    i <= UInt(1)
    wire i0 : UInt<5>
    wire j1 : {a:UInt<2>,b:UInt<2>}
    wire j2 : {a:UInt<2>,b:UInt<2>}

    i0 <= UInt(10)

    mem m1 : 
       data-type => {a:UInt<2>,b:UInt<2>}
       depth => 32
       reader => r
       readwriter => rw
       read-latency => 0
       write-latency => 1
    m1.r.addr <= i
    m1.r.en <= UInt(1)
    m1.r.clk <= clk
    m1.rw.addr <= i
    m1.rw.mask.a <= UInt(1)
    m1.rw.mask.b <= UInt(1)
    m1.rw.en <= UInt(1)
    m1.rw.clk <= clk
    m1.rw.data.a <= UInt(2)
    m1.rw.data.b <= UInt(2)
    m1.rw.wmode <= UInt(1)
    j <= m1.rw.rdata

    mem m2 : 
       data-type => {a:UInt<2>,b:UInt<2>}
       depth => 32
       reader => r
       writer => w
       read-latency => 0
       write-latency => 1
    m2.r.addr <= i
    m2.r.en <= UInt(1)
    m2.r.clk <= clk
    m2.w.addr <= i
    m2.w.mask.a <= UInt(1)
    m2.w.mask.b <= UInt(1)
    m2.w.en <= UInt(1)
    m2.w.clk <= clk
    m2.w.data.a <= UInt(2)
    m2.w.data.b <= UInt(2)  
    j2 <= m2.r.data
