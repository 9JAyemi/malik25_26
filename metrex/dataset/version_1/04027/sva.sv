// SVA for and_gate
module and_gate_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic B2_N,
  input logic Y
);

  // Functional correctness (4-state)
  assert property (@(*) Y === ~(A1 & A2 & B1_N & B2_N));

  // Deterministic cases
  assert property (@(*) ((!A1 || !A2 || !B1_N || !B2_N) |-> (Y === 1'b1)));
  assert property (@(*) ((A1===1'b1 && A2===1'b1 && B1_N===1'b1 && B2_N===1'b1) |-> (Y === 1'b0)));

  // No X/Z on Y when inputs are all known
  assert property (@(*) ((!$isunknown({A1,A2,B1_N,B2_N})) |-> !$isunknown(Y)));

  // X-propagation in fully-sensitive case (other three 1's)
  assert property (@(*) ($isunknown(A1)   && A2===1 && B1_N===1 && B2_N===1 |-> $isunknown(Y)));
  assert property (@(*) ($isunknown(A2)   && A1===1 && B1_N===1 && B2_N===1 |-> $isunknown(Y)));
  assert property (@(*) ($isunknown(B1_N) && A1===1 && A2===1   && B2_N===1 |-> $isunknown(Y)));
  assert property (@(*) ($isunknown(B2_N) && A1===1 && A2===1   && B1_N===1 |-> $isunknown(Y)));

  // Output only changes when some input changes
  assert property (@(*) ($changed(Y) |-> $changed({A1,A2,B1_N,B2_N})));

  // Coverage: all 16 input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_in
      cover property (@(*) {A1,A2,B1_N,B2_N} == i[3:0]);
    end
  endgenerate
  // Coverage: both output polarities and transitions
  cover property (@(*) (Y===1));
  cover property (@(*) (Y===0));
  cover property (@(*) $rose(Y));
  cover property (@(*) $fell(Y));

endmodule

bind and_gate and_gate_sva u_and_gate_sva (
  .A1(A1), .A2(A2), .B1_N(B1_N), .B2_N(B2_N), .Y(Y)
);