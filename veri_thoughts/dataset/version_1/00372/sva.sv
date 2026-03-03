// SVA for two_bit_adder and full_adder
// Bind-only checkers; no DUT edits needed

module two_bit_adder_sva (
  input  logic [1:0] A, B,
  input  logic       cin,
  input  logic [1:0] sum,
  input  logic       cout,
  input  logic [1:0] s1,
  input  logic       c1
);
  // Sample on any input edge
  `define TBA_CHG @(posedge A[0] or negedge A[0] or \
                     posedge A[1] or negedge A[1] or \
                     posedge B[0] or negedge B[0] or \
                     posedge B[1] or negedge B[1] or \
                     posedge cin  or negedge cin)

  function automatic bit known_i; return !$isunknown({A,B,cin}); endfunction
  function automatic bit known_o; return !$isunknown({sum,cout}); endfunction

  // Top-level functional equivalence
  property p_func; `TBA_CHG known_i |-> {cout,sum} == (A + B + cin); endproperty
  assert property (p_func);

  // Outputs must be known when inputs are known
  property p_known; `TBA_CHG known_i |-> known_o; endproperty
  assert property (p_known);

  // Connectivity/ripple structure inside the DUT
  // (Bound in the scope of two_bit_adder; U0/U1 are visible)
  property p_conn;
    `TBA_CHG 1 |-> (sum == {s1[1],s1[0]}) &&
                   (c1 == U0.COUT) &&
                   (U1.CI == c1) &&
                   (s1[0] == U0.SUM) &&
                   (s1[1] == U1.SUM);
  endproperty
  assert property (p_conn);

  // Bit-slice checks (lower and upper full adders)
  property p_bit0; `TBA_CHG known_i |-> {c1, s1[0]} == (A[0] + B[0] + cin); endproperty
  assert property (p_bit0);
  property p_bit1; `TBA_CHG known_i |-> {cout, s1[1]} == (A[1] + B[1] + c1); endproperty
  assert property (p_bit1);

  // Carry classify for bit0: generate/kill/propagate
  assert property (`TBA_CHG known_i && (A[0] & B[0]) |-> c1);
  assert property (`TBA_CHG known_i && (~A[0] & ~B[0]) |-> !c1);
  assert property (`TBA_CHG known_i && (A[0] ^ B[0]) |-> (c1 == cin));

  // Compact functional coverage:
  // - All possible 3-bit results {cout,sum} = 0..5
  genvar v;
  generate
    for (v = 0; v <= 5; v++) begin : C_RESULT
      cover property (`TBA_CHG known_i && {cout,sum} == v[2:0]);
    end
  endgenerate
  // - Key corners and behaviors
  cover property (`TBA_CHG known_i && {A,B,cin} == 5'b00000);
  cover property (`TBA_CHG known_i && {A,B,cin} == 5'b11111);
  cover property (`TBA_CHG known_i && cout);
  cover property (`TBA_CHG known_i && (A[0]^B[0]) && (c1==cin));
  cover property (`TBA_CHG known_i && (A[0]&B[0]) && c1);

  `undef TBA_CHG
endmodule


module full_adder_sva (
  input  logic A, B, CI,
  input  logic SUM, COUT
);
  `define FA_CHG @(posedge A or negedge A or \
                    posedge B or negedge B or \
                    posedge CI or negedge CI)

  function automatic bit known_i; return !$isunknown({A,B,CI}); endfunction
  function automatic bit known_o; return !$isunknown({SUM,COUT}); endfunction

  // Single-bit adder functional equivalence and X-check
  assert property (`FA_CHG known_i |-> {COUT,SUM} == (A + B + CI));
  assert property (`FA_CHG known_i |-> known_o);

  // Full input-space coverage (8 combinations) and output activity
  genvar k;
  generate
    for (k = 0; k < 8; k++) begin : C_VEC
      cover property (`FA_CHG known_i && {A,B,CI} == k[2:0]);
    end
  endgenerate
  cover property (`FA_CHG SUM);
  cover property (`FA_CHG COUT);

  `undef FA_CHG
endmodule


// Bind the checkers
bind two_bit_adder two_bit_adder_sva two_bit_adder_sva_i (
  .A(A), .B(B), .cin(cin), .sum(sum), .cout(cout), .s1(s1), .c1(c1)
);
bind full_adder   full_adder_sva   full_adder_sva_i (.*);