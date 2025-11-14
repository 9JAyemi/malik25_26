// SVA for four_bit_adder and full_adder
// Bind-ready, concise, and covers function and key internals.

module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       CI,
  input logic [3:0] SUM,
  input logic       CO,
  // internal ripple carries
  input logic       C1,
  input logic       C2,
  input logic       C3
);
  // Derived propagate/generate and expected carries
  wire [3:0] P = A ^ B;
  wire [3:0] G = A & B;

  wire c1_exp = G[0] | (P[0] & CI);
  wire c2_exp = G[1] | (P[1] & c1_exp);
  wire c3_exp = G[2] | (P[2] & c2_exp);
  wire c4_exp = G[3] | (P[3] & c3_exp);

  // Functional equivalence (5-bit result)
  property p_add_correct;
    @(*) (!$isunknown({A,B,CI})) |-> ##0 ({CO,SUM} == (A + B + CI));
  endproperty
  assert property (p_add_correct);

  // Ripple-carry chain and sums must match propagate/generate computation
  property p_ripple_and_sum_correct;
    @(*) (!$isunknown({A,B,CI})) |-> ##0
      (CO == c4_exp) &&
      (SUM == {P[3]^c3_exp, P[2]^c2_exp, P[1]^c1_exp, P[0]^CI}) &&
      (C1 == c1_exp) && (C2 == c2_exp) && (C3 == c3_exp);
  endproperty
  assert property (p_ripple_and_sum_correct);

  // No X/Z on outputs when inputs are known
  property p_no_x_when_inputs_known;
    @(*) (!$isunknown({A,B,CI})) |-> ##0 !$isunknown({SUM,CO});
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Carry lookahead form of CO (independent check path)
  property p_co_cla;
    @(*) (!$isunknown({A,B,CI})) |-> ##0
      CO == ( G[3]
           | (P[3] & G[2])
           | (P[3] & P[2] & G[1])
           | (P[3] & P[2] & P[1] & G[0])
           | (P[3] & P[2] & P[1] & P[0] & CI) );
  endproperty
  assert property (p_co_cla);

  // Coverage: hit every possible 5-bit result {CO,SUM}
  genvar r;
  for (r = 0; r < 32; r++) begin : cov_res
    cover property (@(*) ##0 ({CO,SUM} == r[4:0]));
  end

  // Coverage: long propagate chains with/without incoming carry
  cover property (@(*) (P == 4'hF) &&  CI ##0 (CO));
  cover property (@(*) (P == 4'hF) && !CI ##0 (!CO));
endmodule

module full_adder_sva (
  input logic A,
  input logic B,
  input logic CI,
  input logic SUM,
  input logic CO
);
  // Sum parity
  property p_sum_parity;
    @(*) (!$isunknown({A,B,CI})) |-> ##0 (SUM == (A ^ B ^ CI));
  endproperty
  assert property (p_sum_parity);

  // Carry alternative forms (majority / propagate-generate)
  property p_co_pg_form;
    @(*) (!$isunknown({A,B,CI})) |-> ##0 (CO == ((A & B) | (CI & (A ^ B))));
  endproperty
  assert property (p_co_pg_form);

  // No X/Z on outputs when inputs are known
  property p_no_x_when_inputs_known;
    @(*) (!$isunknown({A,B,CI})) |-> ##0 !$isunknown({SUM,CO});
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Cell-level coverage: all 8 input combinations observed
  genvar v;
  for (v = 0; v < 8; v++) begin : cov_tt
    cover property (@(*) ##0 ({A,B,CI} == v[2:0]));
  end
endmodule

// Bind assertions into DUTs
bind four_bit_adder four_bit_adder_sva four_bit_adder_sva_i(.*);
bind full_adder     full_adder_sva     full_adder_sva_i(.*);