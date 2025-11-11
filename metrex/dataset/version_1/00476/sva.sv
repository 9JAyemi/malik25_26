// SVA for top_module hierarchy (bind once; checks PE, BS, and top wiring)
module top_sva (
  input logic         clk,
  input logic         reset,
  input logic [7:0]   in,
  input logic [1:0]   shift_amount,
  input logic         mode,
  input logic [2:0]   pe_out,
  input logic [3:0]   bs_out,
  input logic [7:0]   out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Priority encoder checks (complete partition of input space)
  // 1-hot -> 100
  assert property ($countones(in) == 1 |-> pe_out == 3'b100);
  // 2-hot including in[0] -> 010
  assert property ($countones(in) == 2 && in[0] |-> pe_out == 3'b010);
  // 2-hot including in[1] but not in[0] -> 001
  assert property ($countones(in) == 2 && !in[0] && in[1] |-> pe_out == 3'b001);
  // 2-hot with neither in[0] nor in[1] -> 000
  assert property ($countones(in) == 2 && !in[0] && !in[1] |-> pe_out == 3'b000);
  // 0-hot -> 000
  assert property ($countones(in) == 0 |-> pe_out == 3'b000);
  // 3-or-more hot -> 000
  assert property ($countones(in) >= 3 |-> pe_out == 3'b000);

  // Barrel shifter checks
  // Clean mode (0/1) — exact shift behavior
  assert property (!$isunknown(mode) && !$isunknown(shift_amount)
                   |-> bs_out == (mode ? (in[3:0] >> shift_amount)
                                       : (in[3:0] << shift_amount)));
  // X/Z mode — passthrough
  assert property ($isunknown(mode) |-> bs_out == in[3:0]);

  // Top-level concatenation/wiring (note zero-extend MSB)
  assert property (out == {1'b0, pe_out, bs_out});

  // Sanity: known inputs imply known output
  assert property ((!$isunknown(in) && !$isunknown(shift_amount) && !$isunknown(mode)) |-> !$isunknown(out));

  // Functional coverage (essential scenarios)
  cover property ($countones(in) == 0);
  cover property ($countones(in) == 1);
  cover property ($countones(in) == 2 && in[0]);
  cover property ($countones(in) == 2 && !in[0] && in[1]);
  cover property ($countones(in) == 2 && !in[0] && !in[1]);
  cover property ($countones(in) >= 3);

  cover property (mode==1'b0 && shift_amount==2'd0);
  cover property (mode==1'b0 && shift_amount==2'd1);
  cover property (mode==1'b0 && shift_amount==2'd2);
  cover property (mode==1'b0 && shift_amount==2'd3);

  cover property (mode==1'b1 && shift_amount==2'd0);
  cover property (mode==1'b1 && shift_amount==2'd1);
  cover property (mode==1'b1 && shift_amount==2'd2);
  cover property (mode==1'b1 && shift_amount==2'd3);
endmodule

bind top_module top_sva u_top_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .shift_amount(shift_amount),
  .mode(mode),
  .pe_out(priority_encoder_out),
  .bs_out(barrel_shifter_out),
  .out(out)
);