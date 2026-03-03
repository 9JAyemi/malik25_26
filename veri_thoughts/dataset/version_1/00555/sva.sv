// SVA for ripple_carry_adder and full_adder

module rca_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Ci,
  input  logic [3:0] S,
  input  logic       Co,
  input  logic [3:0] C
);
  function automatic logic carry3 (input logic a, b, ci);
    return (a & b) | (a & ci) | (b & ci);
  endfunction

  // Functional correctness
  a_sum: assert property (@(*)
    {Co,S} == ({1'b0,A} + {1'b0,B} + Ci)
  );

  // Internal carry chain correctness
  a_c1: assert property (@(*)
    C[1] == carry3(A[0], B[0], Ci)
  );
  a_c2: assert property (@(*)
    C[2] == carry3(A[1], B[1], C[1])
  );
  a_c3: assert property (@(*)
    C[3] == carry3(A[2], B[2], C[2])
  );
  a_co: assert property (@(*)
    Co   == carry3(A[3], B[3], C[3])
  );

  // X-propagation: clean outputs when inputs are known
  a_known: assert property (@(*)
    !($isunknown({A,B,Ci})) |-> !($isunknown({S,Co,C[3:1]}))
  );

  // Targeted scenario coverage
  cover_zero:    cover property (@(*) (A==4'h0) && (B==4'h0) && !Ci && (S==4'h0) && !Co);
  cover_ripple:  cover property (@(*) (A==4'hF) && (B==4'h0) &&  Ci && (S==4'h0) &&  Co); // full propagate
  cover_max:     cover property (@(*) (A==4'hF) && (B==4'hF) &&  Ci && (S==4'hF) &&  Co); // max+carry

  // Bit-level toggling coverage
  genvar i;
  generate
    for (i=0; i<4; i++) begin : g_s_cov
      cover_s1: cover property (@(*) S[i]);
      cover_s0: cover property (@(*) !S[i]);
    end
  endgenerate
  genvar j;
  generate
    for (j=1; j<4; j++) begin : g_c_cov
      cover_c1: cover property (@(*) C[j]);
      cover_c0: cover property (@(*) !C[j]);
    end
  endgenerate
  cover_co1: cover property (@(*) Co);
  cover_co0: cover property (@(*) !Co);
endmodule


module fa_sva (
  input logic A, B, Ci,
  input logic S, Co
);
  a_fa:    assert property (@(*) {Co,S} == ({1'b0,A} + {1'b0,B} + {1'b0,Ci}));
  a_known: assert property (@(*) !($isunknown({A,B,Ci})) |-> !($isunknown({S,Co})));

  cover_s1:  cover property (@(*) S);
  cover_s0:  cover property (@(*) !S);
  cover_co1: cover property (@(*) Co);
  cover_co0: cover property (@(*) !Co);
endmodule


// Bind assertions into DUTs
bind ripple_carry_adder rca_sva u_rca_sva (.* , .C(C));
bind full_adder        fa_sva  u_fa_sva  (.*);