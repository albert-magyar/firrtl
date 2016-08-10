circuit Top : 
  module Top : 
    input clk : Clock
    output dout : {a:UInt<2>,b:UInt<2>}
    input addr : UInt<5>
    
    mem m1 : 
       data-type => {a:UInt<2>,b:UInt<2>}
       depth => 32
       reader => r
       read-latency => 0
       write-latency => 1
    m1.r.addr <= addr
    m1.r.en <= UInt(1)
    m1.r.clk <= clk
    dout <= m1.r.data
 