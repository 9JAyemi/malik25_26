// SVA for two_bit_adder
// Bind-in checker; purely combinational sampling using @(*)

module two_bit_adder_sva (
  input [1:0] A,
  input [1:0] B,
  input [1:0] S,
  input       C
);

  // Correctness: 3-bit result must match A+B
  property p_fullsum;
    @(*) (!$isunknown({A,B})) |-> {C,S} == (A + B);
  endproperty
  assert property (p_fullsum);

  // LSB parity check
  assert property (@(*) (!$isunknown({A,B})) |-> S[0] == (A[0] ^ B[0]));

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({A,B})) |-> !$isunknown({C,S}));

  // Outputs change only when inputs change
  assert property (@(*) $stable({A,B}) |-> $stable({C,S}));

  // Functional coverage: exercise all 16 input combinations
  genvar ia, ib;
  generate
    for (ia = 0; ia < 4; ia++) begin : gA
      for (ib = 0; ib < 4; ib++) begin : gB
        localparam [1:0] A_CONST = ia;
        localparam [1:0] B_CONST = ib;
        cover property (@(*) (A == A_CONST && B == B_CONST));
      end
    end
  endgenerate

  // Coverage: observe all possible 3-bit sums (0..6)
  genvar is;
  generate
    for (is = 0; is < 7; is++) begin : gSUM
      localparam [2:0] SUM_CONST = is[2:0];
      cover property (@(*) {C,S} == SUM_CONST);
    end
  endgenerate

endmodule

bind two_bit_adder two_bit_adder_sva u_two_bit_adder_sva (.A(A), .B(B), .S(S), .C(C));