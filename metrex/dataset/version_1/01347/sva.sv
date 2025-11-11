// SVA for nand4: checks internal wiring and the intended 4‑input NAND spec.
// Bind gives access to DUT internals AB, CD, ABCD.

module nand4_sva (
  input logic A, B, C, D,
  input logic Y,
  input logic AB, CD, ABCD
);
  // Sample on any input edge; use ##0 in assertions to allow combinational settle
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Functional spec: Y must be 4-input NAND of A,B,C,D (will flag the current RTL bug)
  a_func:    assert property ( (!$isunknown({A,B,C,D})) |-> ##0 (Y == ~(A & B & C & D)) );

  // Internal logic correctness
  a_ab:      assert property ( (!$isunknown({A,B}))     |-> ##0 (AB == ~(A & B)) );
  a_cd:      assert property ( (!$isunknown({C,D}))     |-> ##0 (CD == ~(C & D)) );
  a_abcd:    assert property ( (!$isunknown({AB,CD}))   |-> ##0 (ABCD == ~(AB & CD)) );
  a_y_chain: assert property ( (!$isunknown(ABCD))      |-> ##0 (Y == ~ABCD) );
  // Structural consequence of the two inverters on ABCD
  a_y_and:   assert property ( (!$isunknown({AB,CD}))   |-> ##0 (Y == (AB & CD)) );

  // Known-value propagation (no X/Z) when drivers are known
  a_no_x_ab:   assert property ( (!$isunknown({A,B}))   |-> ##0 !$isunknown(AB) );
  a_no_x_cd:   assert property ( (!$isunknown({C,D}))   |-> ##0 !$isunknown(CD) );
  a_no_x_abcd: assert property ( (!$isunknown({AB,CD})) |-> ##0 !$isunknown(ABCD) );
  a_no_x_y:    assert property ( (!$isunknown(ABCD))    |-> ##0 !$isunknown(Y) );

  // Coverage: observe both output polarities and key scenarios
  c_y0: cover property ( (!$isunknown({A,B,C,D})) && (A & B & C & D) ##0 (Y==0) );
  c_y1: cover property ( (!$isunknown({A,B,C,D})) && (~(A & B & C & D)) ##0 (Y==1) );

  // Drive the "last 1" to reach all-ones from a single-zero state (any latency)
  c_single_zero_a: cover property ( (!A &&  B &&  C &&  D) ##[1:$] (A) ##0 (Y==0) );
  c_single_zero_b: cover property ( ( A && !B &&  C &&  D) ##[1:$] (B) ##0 (Y==0) );
  c_single_zero_c: cover property ( ( A &&  B && !C &&  D) ##[1:$] (C) ##0 (Y==0) );
  c_single_zero_d: cover property ( ( A &&  B &&  C && !D) ##[1:$] (D) ##0 (Y==0) );
endmodule

bind nand4 nand4_sva u_nand4_sva(.A(A),.B(B),.C(C),.D(D),.Y(Y),.AB(AB),.CD(CD),.ABCD(ABCD));