// SVA for initiator
module initiator_sva (initiator dut);
  default clocking @(posedge dut.clk); endclocking

  // Reset drives known zero state next cycle
  assert property (dut.rst |=> (dut.counter==0 && dut.req==0 && dut.dataValid==0 && dut.dataExpect==0));

  // dataValid is previous (req & ~res)
  assert property (disable iff (dut.rst) 1'b1 |=> (dut.dataValid == $past(dut.req & ~dut.res)));

  // Hold when res==1
  assert property (disable iff (dut.rst) dut.res |=> (dut.req==$past(dut.req) &&
                                                     dut.dataExpect==$past(dut.dataExpect) &&
                                                     dut.counter==$past(dut.counter) &&
                                                     dut.dataValid==1'b0));

  // Update when res==0 (NBA semantics)
  assert property (disable iff (dut.rst) ~dut.res |=> (dut.req==$past(dut.counter[0]) &&
                                                       dut.dataExpect==$past(dut.req) &&
                                                       dut.counter==$past(dut.counter)+1 &&
                                                       dut.dataValid==$past(dut.req)));

  // valid behavior: forced low when dataValid, otherwise holds
  assert property (disable iff (dut.rst) dut.dataValid |=> (dut.valid==1'b0));
  assert property (disable iff (dut.rst) !dut.dataValid |=> $stable(dut.valid));

  // req LSB toggles on each increment cycle
  assert property (disable iff (dut.rst) ~dut.res |=> (dut.req == ~$past(dut.req)));

  // Known-ness (post-reset)
  assert property (disable iff (dut.rst) !$isunknown({dut.req, dut.dataValid, dut.res, dut.counter}));

  // Coverage
  cover property (disable iff (dut.rst) ~dut.res ##1 dut.dataValid);
  cover property (disable iff (dut.rst) dut.dataValid && (dut.dataExpect == dut.res));
  cover property (disable iff (dut.rst) dut.dataValid && (dut.dataExpect != dut.res));
  cover property (disable iff (dut.rst) ~dut.res ##1 (dut.counter == $past(dut.counter)+1));
endmodule

bind initiator initiator_sva sva_initiator();