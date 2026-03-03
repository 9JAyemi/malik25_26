// SVA for adder16
module adder16_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic [15:0] Z
);
  default clocking cb @(posedge clk); endclocking

  // Track $past() validity
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // No X on rst and Z after first sampled cycle
  assert property (past_valid |-> !$isunknown(rst));
  assert property (past_valid |-> !$isunknown(Z));

  // Inputs must be known when they are used (previous cycle not in reset)
  assert property (past_valid && !$past(rst) |-> !$isunknown({A,B}));

  // Functional correctness: registered sum with synchronous reset
  assert property (past_valid |-> Z == ($past(rst) ? 16'h0000 : ($past(A) + $past(B))));

  // Reset drives zero on next cycle (redundant but explicit)
  assert property (past_valid && rst |=> Z == 16'h0000);

  // Coverage
  cover property (past_valid ##1 rst ##1 !rst);                                   // reset deassertion
  cover property (past_valid && !$past(rst) && ($past(A)==16'h0000) && ($past(B)==16'h0000) ##1 (Z==16'h0000));
  cover property (past_valid && !$past(rst) && ($past(A)==16'hFFFF) && ($past(B)==16'h0001) ##1 (Z==16'h0000)); // wrap-around
  cover property (past_valid && !$past(rst) && ($past(A)!=16'h0000 || $past(B)!=16'h0000) ##1 (Z==$past(A)+$past(B)));
endmodule

// Bind into DUT
module adder16_bind;
  bind adder16 adder16_sva sva_i (.*);
endmodule