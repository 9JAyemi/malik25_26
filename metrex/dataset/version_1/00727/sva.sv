// SVA for nand3b and nand4
// Focus: functional correctness, power-rail sanity, X-prop, concise coverage.
// Bind these to your DUT after compilation.

////////////////////////////////////////////////////////////
// nand3b assertions
////////////////////////////////////////////////////////////
module nand3b_sva (
  input logic A_N, B, C,
  input logic Y
);
  // Functional truth with 0-delay settle on any input change
  assert property (@(A_N or B or C)
                   !$isunknown({A_N,B,C}) |-> ##0 (Y === ~(A_N & B & C)))
    else $error("nand3b: functional mismatch A_N=%b B=%b C=%b Y=%b", A_N,B,C,Y);

  // No X on Y when inputs are known
  assert property (@(A_N or B or C)
                   !$isunknown({A_N,B,C}) |-> ##0 !$isunknown(Y))
    else $error("nand3b: X/Z on Y with known inputs");

  // Minimal coverage: low and high output corners
  cover property (@(A_N or B or C) (A_N && B && C) ##0 (Y==1'b0)); // all ones -> 0
  cover property (@(A_N or B or C) (!A_N && B && C) ##0 (Y==1'b1)); // single 0 on A_N
  cover property (@(A_N or B or C) (A_N && !B && C) ##0 (Y==1'b1)); // single 0 on B
  cover property (@(A_N or B or C) (A_N && B && !C) ##0 (Y==1'b1)); // single 0 on C
endmodule

bind nand3b nand3b_sva u_nand3b_sva (.A_N(A_N), .B(B), .C(C), .Y(Y));

////////////////////////////////////////////////////////////
// nand4 assertions
////////////////////////////////////////////////////////////
module nand4_sva (
  input  logic A,B,C,D,
  input  logic VPWR, VGND, VPB, VNB,
  input  logic Y
);
  logic power_good, inputs_known, rails_known;
  assign rails_known  = !$isunknown({VPWR,VGND,VPB,VNB});
  assign power_good   = rails_known && (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  assign inputs_known = !$isunknown({A,B,C,D});

  // Rails must be known (no X/Z) whenever they change
  assert property (@(VPWR or VGND or VPB or VNB) rails_known)
    else $error("nand4: rails contain X/Z: VPWR=%b VGND=%b VPB=%b VNB=%b", VPWR,VGND,VPB,VNB);

  // Core functional check of a 4-input NAND under good rails and known inputs
  assert property (@(A or B or C or D or VPWR or VGND or VPB or VNB)
                   (power_good && inputs_known) |-> ##0 (Y === ~(A & B & C & D)))
    else $error("nand4: functional mismatch: A=%b B=%b C=%b D=%b Y=%b", A,B,C,D,Y);

  // No X on Y when rails good and inputs known
  assert property (@(A or B or C or D or VPWR or VGND or VPB or VNB)
                   (power_good && inputs_known) |-> ##0 !$isunknown(Y))
    else $error("nand4: X/Z on Y with good power and known inputs");

  // Basic power sanity: only legal power combo is 1/0/1/0
  assert property (@(VPWR or VGND or VPB or VNB)
                   (rails_known) |-> ((VPWR==1'b1 && VGND==1'b0 && VPB==1'b1 && VNB==1'b0) ||
                                      (VPWR==1'b0 || VGND==1'b1))) // allow off/illegal rails without failing functionality
    else $warning("nand4: unexpected rail combo VPWR=%b VGND=%b VPB=%b VNB=%b", VPWR,VGND,VPB,VNB);

  // Minimal functional coverage under good rails
  //  - output low corner (all inputs 1)
  cover property (@(A or B or C or D) power_good && inputs_known && (&{A,B,C,D}) ##0 (Y==1'b0));
  //  - each single-0 input case yields Y==1
  cover property (@(A or B or C or D) power_good && inputs_known && (!A &&  B &&  C &&  D) ##0 (Y==1'b1));
  cover property (@(A or B or C or D) power_good && inputs_known && ( A && !B &&  C &&  D) ##0 (Y==1'b1));
  cover property (@(A or B or C or D) power_good && inputs_known && ( A &&  B && !C &&  D) ##0 (Y==1'b1));
  cover property (@(A or B or C or D) power_good && inputs_known && ( A &&  B &&  C && !D) ##0 (Y==1'b1));
  //  - Y toggles both ways at least once under good rails
  cover property (@(posedge Y) power_good && inputs_known);
  cover property (@(negedge Y) power_good && inputs_known);
endmodule

bind nand4 nand4_sva u_nand4_sva (.A(A),.B(B),.C(C),.D(D),
                                   .VPWR(VPWR),.VGND(VGND),.VPB(VPB),.VNB(VNB),
                                   .Y(Y));