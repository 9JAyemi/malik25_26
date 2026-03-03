// SVA for Adder
// Bind this module to the DUT. Provide clk/rst_n from your environment.

module Adder_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [19:0] Data_A_i,
  input logic [19:0] Data_B_i,
  input logic [20:0] O,
  input logic        CO,
  input logic [3:0]  S,
  input logic [3:0]  DI
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity (no X/Z on outputs when inputs are known)
  assert property (!$isunknown({Data_A_i,Data_B_i}) |-> !$isunknown({O,CO,S,DI}));

  // Arithmetic correctness
  assert property (O == Data_A_i + Data_B_i);
  assert property (CO == O[20]);
  assert property (S == (O[3:0] + CO)[3:0]);
  assert property (DI == {CO, S[3:1]});

  // Cross-consistency (redundant guardrails, still concise)
  assert property ({CO, O[19:0]} == (Data_A_i + Data_B_i));

  // Coverage
  cover property (!CO);                              // no carry
  cover property (CO);                               // carry
  cover property (Data_A_i == 20'h0 && Data_B_i == 20'h0);
  cover property (Data_A_i == 20'hFFFFF && Data_B_i == 20'h00001); // overflow case
  cover property (Data_A_i == 20'hFFFFE && Data_B_i == 20'h00001); // boundary no-carry
  cover property (CO && (O[3:0] == 4'hF));           // nibble wrap scenario for S

endmodule

// Example bind (put in your TB/top-level, ensure clk/rst_n are in scope):
// bind Adder Adder_sva u_adder_sva (.* , .clk(clk), .rst_n(rst_n));