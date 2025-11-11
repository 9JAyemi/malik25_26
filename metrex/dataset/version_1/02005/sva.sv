// SVA for sky130_fd_sc_hs__a31o and wrapper hierarchy
// Concise, clockless, combinational correctness checks with essential coverage

// --------------- NOR2 -----------------
module nor2_sva (input A, B, Y);
  // Functional correctness
  assert property ( (!$isunknown({A,B})) |-> (Y === ~(A | B)) )
    else $error("nor2: Y != ~(A|B)");
  // Truth-table coverage
  cover property (A==0 && B==0 && Y==1);
  cover property (A==0 && B==1 && Y==0);
  cover property (A==1 && B==0 && Y==0);
  cover property (A==1 && B==1 && Y==0);
endmodule

// --------------- "NAND2" (actually OR per given RTL) ---------------
module nand2_sva (input A, B, Y);
  // Functional correctness per given implementation
  assert property ( (!$isunknown({A,B})) |-> (Y === (A | B)) )
    else $error("nand2_1: Y != (A|B) per RTL");
  // Output known when inputs known
  assert property ( (!$isunknown({A,B})) |-> !$isunknown(Y) );
  // Coverage: both output values
  cover property (A==0 && B==0 && Y==0);
  cover property ((A^B) && Y==1);
  cover property (A==1 && B==1 && Y==1);
endmodule

// --------------- "AND2" (actually NOR per given RTL) ---------------
module and2_sva (input A, B, X);
  // Functional correctness per given implementation
  assert property ( (!$isunknown({A,B})) |-> (X === ~(A | B)) )
    else $error("and2_1: X != ~(A|B) per RTL");
  // Output known when inputs known
  assert property ( (!$isunknown({A,B})) |-> !$isunknown(X) );
  // Coverage: both output values
  cover property (A==0 && B==0 && X==1);
  cover property ((A|B)==1 && X==0);
endmodule

// --------------- A31O leaf (built from 3 NOR-like stages per RTL) ---------------
module a31o_sva (
  input VPWR, VGND,
  input A1, A2, A3, B1,
  input X,
  input n1, n2, n3
);
  // Power assumptions (optional but recommended)
  assume property (VPWR === 1'b1);
  assume property (VGND === 1'b0);

  // Stage-wise local correctness (matches given RTL)
  assert property ( (!$isunknown({A1,A2}))      |-> (n1 === ~(A1 | A2)) ) else $error("a31o.n1 mismatch");
  assert property ( (!$isunknown({n1,A3}))      |-> (n2 === ~(n1 | A3)) ) else $error("a31o.n2 mismatch");
  assert property ( (!$isunknown({B1,n2}))      |-> (n3 === ~(B1 | n2)) ) else $error("a31o.n3 mismatch");
  assert property ( (n3 === X) ) else $error("a31o.X != n3");

  // End-to-end X function (collapsed expression from the RTL)
  assert property ( (!$isunknown({A1,A2,A3,B1})) |-> ( X === ~( B1 | ~( (~(A1 | A2)) | A3 ) ) ) )
    else $error("a31o.X end-to-end mismatch");

  // Coverage: exercise key minterms and both X polarities
  cover property (A1==0 && A2==0 && A3==0 && B1==0 && X==1);
  cover property (A1==1 && A2==1 && A3==1 && B1==1 && X==0);
  cover property (X==0);
  cover property (X==1);
endmodule

// --------------- Wrapper (mux between X and ~X) ---------------
module a31o_wrapper_sva (
  input VPWR, VGND,
  input A1, A2, A3, B1,
  input SEL,
  input Y,
  input X,        // internal from instance
  input not_X     // internal complement
);
  // Power assumptions
  assume property (VPWR === 1'b1);
  assume property (VGND === 1'b0);

  // Internal complement correctness
  assert property ( (!$isunknown(X)) |-> (not_X === ~X) ) else $error("wrapper.not_X != ~X");
  assert property ( (!$isunknown({SEL,X})) |-> (Y === (SEL ? ~X : X)) ) else $error("wrapper.Y mux mismatch");

  // Compact equivalence: Y ^ X equals SEL
  assert property ( (!$isunknown({SEL,X})) |-> ((Y ^ X) === SEL) ) else $error("wrapper.Y^X != SEL");

  // Coverage: both mux paths and both X polarities
  cover property (SEL==0 && Y===X);
  cover property (SEL==1 && Y===~X);
  cover property (X==0 && not_X==1);
  cover property (X==1 && not_X==0);
endmodule

// ---------------- Binds ----------------
bind sky130_fd_sc_hs__nor2_1    nor2_sva       nor2_sva_i   (.A(A), .B(B), .Y(Y));
bind sky130_fd_sc_hs__nand2_1   nand2_sva      nand2_sva_i  (.A(A), .B(B), .Y(Y));
bind sky130_fd_sc_hs__and2_1    and2_sva       and2_sva_i   (.A(A), .B(B), .X(X));
bind sky130_fd_sc_hs__a31o      a31o_sva       a31o_sva_i   (.VPWR(VPWR), .VGND(VGND), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .X(X), .n1(n1), .n2(n2), .n3(n3));
bind sky130_fd_sc_hs__a31o_wrapper a31o_wrapper_sva a31o_wrapper_sva_i (.VPWR(VPWR), .VGND(VGND), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .SEL(SEL), .Y(Y), .X(X), .not_X(not_X));