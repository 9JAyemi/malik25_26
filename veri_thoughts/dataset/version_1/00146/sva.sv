// SVA for adder. Focused, high-quality checks and coverage.
// Bind into DUT; no DUT/testbench changes required.

module adder_sva (
  input logic [3:0] A, B,
  input logic [3:0] S,
  input logic       C
);
  // Fire an event on any combinational activity for clockless SVA
  event comb_ev;
  always @* -> comb_ev;

  function automatic logic [4:0] sum5(input logic [3:0] a, b);
    return {1'b0, a} + {1'b0, b};
  endfunction

  // Golden functional check: 5-bit result must match
  property p_sum_correct;
    @(comb_ev) !$isunknown({A,B}) |-> {C,S} == sum5(A,B);
  endproperty
  assert property (p_sum_correct);

  // X-prop: known inputs imply known outputs
  property p_outputs_known_when_inputs_known;
    @(comb_ev) !$isunknown({A,B}) |-> !$isunknown({C,S});
  endproperty
  assert property (p_outputs_known_when_inputs_known);

  // Coverage: exercise carry/no-carry and key boundaries
  cover property (@(comb_ev) sum5(A,B)[4] && C);                 // carry-out observed (and consistent)
  cover property (@(comb_ev) !sum5(A,B)[4] && !C);               // no carry-out observed (and consistent)
  cover property (@(comb_ev) A==4'h0 && B==4'h0 && {C,S}==5'h00);
  cover property (@(comb_ev) A==4'hF && B==4'h1 && {C,S}==5'h10);
  cover property (@(comb_ev) A==4'hF && B==4'hF && {C,S}==5'h1E);
endmodule

bind adder adder_sva u_adder_sva(.A(A), .B(B), .S(S), .C(C));