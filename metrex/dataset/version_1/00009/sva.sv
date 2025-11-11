// SVA for softusb_filter
// Binds to the DUT and checks sampling/delay behavior and basic X-propagation.

module softusb_filter_sva (softusb_filter dut);
  default clocking cb @(posedge dut.usb_clk); endclocking

  bit past1, past2;
  always @(posedge dut.usb_clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Stage-0 flops capture inputs (1-cycle past in SVA sampling domain)
  assert property (disable iff (!past1) dut.rcv_s0 == $past(dut.rcv));
  assert property (disable iff (!past1) dut.vp_s0  == $past(dut.vp));
  assert property (disable iff (!past1) dut.vm_s0  == $past(dut.vm));

  // Outputs equal inputs delayed by two sampled cycles (due to SVA preponed sampling)
  assert property (disable iff (!past2) dut.rcv_s == $past(dut.rcv,2));
  assert property (disable iff (!past2) dut.vp_s  == $past(dut.vp,2));
  assert property (disable iff (!past2) dut.vm_s  == $past(dut.vm,2));

  // Known-propagation: known input -> known output on the next cycle
  assert property (disable iff (!past1) !$isunknown($past(dut.rcv)) |-> ##1 !$isunknown(dut.rcv_s));
  assert property (disable iff (!past1) !$isunknown($past(dut.vp))  |-> ##1 !$isunknown(dut.vp_s));
  assert property (disable iff (!past1) !$isunknown($past(dut.vm))  |-> ##1 !$isunknown(dut.vm_s));

  // Coverage: edge propagation to outputs one cycle later
  cover property ($rose(dut.rcv) ##1 $rose(dut.rcv_s));
  cover property ($fell(dut.rcv) ##1 $fell(dut.rcv_s));
  cover property ($rose(dut.vp)  ##1 $rose(dut.vp_s));
  cover property ($fell(dut.vp)  ##1 $fell(dut.vp_s));
  cover property ($rose(dut.vm)  ##1 $rose(dut.vm_s));
  cover property ($fell(dut.vm)  ##1 $fell(dut.vm_s));
endmodule

bind softusb_filter softusb_filter_sva sva_softusb_filter();