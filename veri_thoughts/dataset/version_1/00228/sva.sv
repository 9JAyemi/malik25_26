// SVA for and_logic
module and_logic_sva #(parameter int W=4) (
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic         reset,
  input logic [W-1:0] C
);
  // Sample on any input change; ##0 aligns with NBA update of C
  default clocking cb @(A or B or reset); endclocking

  // Functional correctness (including X-propagation) after delta
  assert property (1'b1 |-> ##0 (reset ? (C === '0) : (C === (A & B))));

  // Known-ness when inputs are known
  assert property (!reset && !$isunknown({A,B,reset}) |-> ##0 (!$isunknown(C) && (C == (A & B))));
  assert property (reset && !$isunknown(reset)       |-> ##0 (C == '0 && !$isunknown(C)));

  // C must remain zero for the full duration of reset
  assert property (reset |-> ##0 ((C === '0) throughout reset));

  // Bit-level functional coverage
  genvar i;
  generate for (i=0; i<W; i++) begin : g_cov
    cover property (!reset && A[i] && B[i] |-> ##0  C[i]);     // AND=1 case
    cover property (!reset && (!A[i] || !B[i]) |-> ##0 !C[i]); // AND=0 case
  end endgenerate

  // Corner coverage
  cover property (!reset && A == '0 && B == '0 |-> ##0 C == '0);
  cover property (!reset && A == '1 && B == '1 |-> ##0 C == '1);
  cover property ($rose(reset) ##1 $fell(reset)); // observe a reset pulse
endmodule

bind and_logic and_logic_sva #(.W(4)) u_and_logic_sva (.*);