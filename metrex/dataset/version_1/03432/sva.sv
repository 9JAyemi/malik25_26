// SVA for top_module
module top_module_sva;
  // Bind into DUT scope to access internals
  bind top_module top_module_sva_i();
endmodule

module top_module_sva_i;
  // Access DUT signals directly (we are bound inside top_module)
  // Clocking
  default clocking cb @(posedge clk); endclocking

  // Local lets for clarity
  let xor0     = a ^ b;
  let xor1     = c ^ d;
  let mult_exp = (xor0 ^ xor1) & counter[0];  // Matches DUT’s effective LSB behavior
  let q_exp    = {2'b00, mult_out};

  // Counter behavior
  assert property (@cb reset |-> counter == 4'd0);
  assert property (@cb !reset && !$past(reset) |-> counter == $past(counter) + 4'd1);

  // counter_out wiring
  assert property (@cb counter_out[2:0] == counter[2:0]);
  assert property (@cb counter_out[3]   == 1'b0);

  // XOR outputs
  assert property (@cb xor_out == {xor0, xor1});

  // mult_out functional check (concise, LSB-equivalent)
  assert property (@cb mult_out == mult_exp);

  // q behavior under control
  // When control is high, q must reflect zero-extended mult_out immediately at the sample
  assert property (@cb control |-> q == q_exp);
  // When control remains low, q holds its value
  assert property (@cb !control && !$past(control) |-> q == $past(q));

  // No X/Z on q when control is asserted
  assert property (@cb control |-> !$isunknown(q));

  // Sanity: continuous assignment connectivity
  // Note: q should always mirror q_reg
  always @* assert (q == q_reg);

  // Coverage
  cover property (@cb reset ##1 !reset);                                // reset release
  cover property (@cb !reset ##[1:$] counter==4'hF ##1 counter==4'h0);  // counter wrap
  cover property (@cb (xor0^xor1) && counter[0]);                       // mult_out can be 1
  cover property (@cb !(xor0^xor1) || !counter[0]);                     // mult_out can be 0
  cover property (@cb $rose(control));                                   // control rises
  cover property (@cb control && $changed(mult_out) && $changed(q));     // q updates under control
endmodule