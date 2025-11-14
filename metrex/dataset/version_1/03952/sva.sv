// SVA checker for and4_2and
module and4_2and_sva (
  input logic A, B, C, D,
  input logic X,
  input logic AB, CD, ABCD
);
  // Sample on any input edge; use ##0 to avoid preponed sampling race
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Structural/functional correctness
  ap_ab:    assert property ( (!$isunknown({A,B}))     |-> ##0 (AB    === (A & B)) );
  ap_cd:    assert property ( (!$isunknown({C,D}))     |-> ##0 (CD    === (C & D)) );
  ap_abcd:  assert property ( (!$isunknown({AB,CD}))   |-> ##0 (ABCD  === (AB & CD)) );
  ap_xconn: assert property (                             ##0 (X     === ABCD) );
  ap_xfunc: assert property ( (!$isunknown({A,B,C,D})) |-> ##0 (X     === (A & B & C & D)) );

  // No X/Z on internal/output when inputs are known
  ap_known: assert property ( (!$isunknown({A,B,C,D})) |-> ##0 (!$isunknown({AB,CD,ABCD,X})) );

  // Full input-space coverage (all 16 combinations)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_vec
      cover property ( ##0 {A,B,C,D} === i[3:0] );
    end
  endgenerate

  // Sanity coverage on output
  cx1: cover property ( ##0 X == 1'b1 );
  cx0: cover property ( ##0 X == 1'b0 );
endmodule

// Bind into DUT to observe internal nets
bind and4_2and and4_2and_sva u_and4_2and_sva (
  .A(A), .B(B), .C(C), .D(D),
  .X(X),
  .AB(AB), .CD(CD), .ABCD(ABCD)
);