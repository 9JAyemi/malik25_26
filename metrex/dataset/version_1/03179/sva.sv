// SVA checker for bm_stmt_compare_padding
module bm_stmt_compare_padding_sva (
  input logic        clock,
  input logic        reset_n,
  input logic [2:0]  a_in,
  input logic [1:0]  b_in,
  input logic [3:0]  out0,
  input logic        out1,
  input logic        out5,
  input logic [3:0]  out6,
  input logic        out7,
  input logic [3:0]  out8
);

  default clocking cb @(posedge clock); endclocking
  default disable iff (!reset_n);

  // Functional correctness (use $past on inputs to align with flop update)
  assert property ($past(reset_n) |-> out0 == (4'hF - {1'b0, $past(a_in)}));
  assert property ($past(reset_n) |-> out1 == ($past(b_in) == 2'b00));
  assert property ($past(reset_n) |-> out5 == ($past(b_in) == 2'b00));
  assert property ($past(reset_n) |-> out6 == (($past(b_in) == 2'b00) ? 4'b0001 : 4'b0000));

  // out7/out8 behavior given the coded case ordering
  assert property ($past(reset_n) |-> out7 == 1'b1);
  assert property ($past(reset_n) |-> out8 == (($past(a_in) == 3'b000) ? 4'b0001 : 4'b0000));
  assert property ($past(reset_n) |-> out8 != 4'b0100); // unreachable branch

  // Cross-signal consistency
  assert property (out1 == out5);
  assert property (out6 == {3'b000, out5});

  // No X/Z on outputs after reset release
  assert property ($past(reset_n) |-> !$isunknown({out0,out1,out5,out6,out7,out8}));

  // Functional coverage
  cover property ($past(reset_n) && $past(a_in)==3'd0 && out0==4'b1111);
  cover property ($past(reset_n) && $past(a_in)==3'd1 && out0==4'b1110);
  cover property ($past(reset_n) && $past(a_in)==3'd2 && out0==4'b1101);
  cover property ($past(reset_n) && $past(a_in)==3'd3 && out0==4'b1100);
  cover property ($past(reset_n) && $past(a_in)==3'd4 && out0==4'b1011);
  cover property ($past(reset_n) && $past(a_in)==3'd5 && out0==4'b1010);
  cover property ($past(reset_n) && $past(a_in)==3'd6 && out0==4'b1001);
  cover property ($past(reset_n) && $past(a_in)==3'd7 && out0==4'b1000);

  cover property ($past(reset_n) && $past(b_in)==2'b00 && out1 && out5 && out6==4'b0001);
  cover property ($past(reset_n) && $past(b_in)==2'b01 && !out1 && !out5 && out6==4'b0000);
  cover property ($past(reset_n) && $past(b_in)==2'b10 && !out1 && !out5 && out6==4'b0000);
  cover property ($past(reset_n) && $past(b_in)==2'b11 && !out1 && !out5 && out6==4'b0000);

  cover property ($past(reset_n) && $past(a_in)==3'b000 && out8==4'b0001);
  cover property ($past(reset_n) && $past(a_in)!=3'b000 && out8==4'b0000);

endmodule

// Bind into DUT
bind bm_stmt_compare_padding bm_stmt_compare_padding_sva sva_i (
  .clock (clock),
  .reset_n (reset_n),
  .a_in (a_in),
  .b_in (b_in),
  .out0 (out0),
  .out1 (out1),
  .out5 (out5),
  .out6 (out6),
  .out7 (out7),
  .out8 (out8)
);