// SVA for shift_register
module shift_register_sva;
  // Bound into shift_register scope; direct access to DUT signals
  localparam int DIN_W  = $bits(din_shr);
  localparam int DOUT_W = $bits(dout_shr);

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Sanity: no X/Z on inputs and state after first cycle
  assert property (!$isunknown({stb, di})));
  assert property (!$isunknown({din_shr, dout_shr, din, dout, do})));

  // Core shift behavior
  assert property (din_shr  == {$past(din_shr)[DIN_W-2:0],  $past(di)});
  assert property (dout_shr == {$past(dout_shr)[DOUT_W-2:0], $past(din_shr)[DIN_W-1]});

  // Output relation
  assert property (do == $past(dout_shr[DOUT_W-1]));

  // Strobe snapshot semantics
  assert property (stb  |-> (din  == $past(din_shr)));
  assert property (stb  |-> (dout == $past(dout_shr)));
  assert property (!stb |-> (din  == $past(din)));
  assert property (!stb |-> (dout == $past(dout)));

  // Din/dout only change on strobe
  assert property ($changed(din)  |-> $past(stb));
  assert property ($changed(dout) |-> $past(stb));

  // Coverage
  cover property (stb);
  cover property ($rose(di));
  cover property ($fell(di));
  cover property ($rose(do));
  cover property ($fell(do));
  // Show MSB of din_shr feeding LSB of dout_shr on next cycle
  cover property ($past(din_shr[DIN_W-1]) && (dout_shr[0] == 1'b1));
  // Snapshot occurrence
  cover property (stb && (din == $past(din_shr)) && (dout == $past(dout_shr)));
endmodule

bind shift_register shift_register_sva sva_inst();