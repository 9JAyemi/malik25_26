// SVA for sky130_fd_sc_ls__a221o: X = (A1 & A2) | (B1 & B2) | C1

module a221o_sva (
  input logic A1, A2, B1, B2, C1,
  input logic X,
  input logic and0_out, and1_out, or0_out_X,
  input logic VPWR, VGND, VPB, VNB
);

  // Power rails constant
  assert property (@(VPWR or VGND or VPB or VNB)
                   (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0));

  // Internal net correctness
  assert property (@(B1 or B2 or and0_out) ##0 (and0_out  === (B1 & B2)));
  assert property (@(A1 or A2 or and1_out) ##0 (and1_out  === (A1 & A2)));
  assert property (@(and1_out or and0_out or C1 or or0_out_X) ##0
                   (or0_out_X === (and1_out | and0_out | C1)));
  assert property (@(X or or0_out_X) ##0 (X === or0_out_X));

  // Full functional equivalence (ignore when any input is X/Z)
  assert property (@(A1 or A2 or B1 or B2 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,B2,C1}))
                   ##0 (X === ((A1 & A2) | (B1 & B2) | C1)));

  // Monotonic implications
  assert property (@(C1) (C1) |-> ##0 (X));
  assert property (@(A1 or A2) ((A1 && A2)) |-> ##0 (X));
  assert property (@(B1 or B2) ((B1 && B2)) |-> ##0 (X));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   (!C1 && !(A1 && A2) && !(B1 && B2)) |-> ##0 (!X));

  // Known output when inputs known
  assert property (@(A1 or A2 or B1 or B2 or C1 or X)
                   (!$isunknown({A1,A2,B1,B2,C1})) |-> ##0 (!$isunknown(X)));

  // Functional coverage of key cases
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                  (!A1 && !A2 && !B1 && !B2 && !C1 && !X)); // all zero -> X=0
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                  (!A1 && !A2 && !B1 && !B2 &&  C1 &&  X)); // C1 drives X
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                  ( C1==0 && (A1 && A2) && !(B1 && B2) && X)); // A-pair drives X
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                  ( C1==0 && (B1 && B2) && !(A1 && A2) && X)); // B-pair drives X

  // Toggle coverage
  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge B2) 1);
  cover property (@(negedge B2) 1);
  cover property (@(posedge C1) 1);
  cover property (@(negedge C1) 1);
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

endmodule

bind sky130_fd_sc_ls__a221o a221o_sva
  u_a221o_sva (.*,
               .and0_out(and0_out),
               .and1_out(and1_out),
               .or0_out_X(or0_out_X),
               .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB));