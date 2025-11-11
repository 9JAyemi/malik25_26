// SVA checker for logic_operation
module logic_operation_sva (
  input logic A, B, C, D, Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Local function of DUT
  let ab   = (A & B);
  let cd   = (C & D);
  let expr = (ab | cd);

  // Functional equivalence (4-state)
  A_FUNC_EQ: assert property (@(A or B or C or D or Y) Y === expr)
    else $error("logic_operation: Y != (A&B)|(C&D)");

  // No X on Y when inputs are known (2-state check)
  A_NO_X_ON_Y_IF_KNOWN_IN: assert property (@(A or B or C or D or Y)
                                           (!$isunknown({A,B,C,D})) |-> (! $isunknown(Y) && (Y == expr)))
    else $error("logic_operation: Y unknown or incorrect with known inputs");

  // Output must not change unless inputs change
  A_NO_SPURIOUS_Y_CHANGE: assert property (@(A or B or C or D or Y)
                                          $stable({A,B,C,D}) |-> $stable(Y))
    else $error("logic_operation: Y changed without input change");

  // Supply rails sanity (constants and no change)
  initial assert (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
    else $error("logic_operation: supply rails not at expected values at t=0");
  A_SUPPLIES_CONST: assert property (@(VPWR or VPB or VGND or VNB)
                                    VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
    else $error("logic_operation: supply rails changed");

  // Functional coverage
  cover_ab_only: cover property (@(A or B or C or D)  ab && !cd &&  Y);
  cover_cd_only: cover property (@(A or B or C or D)  cd && !ab &&  Y);
  cover_both:    cover property (@(A or B or C or D)  ab &&  cd &&  Y);
  cover_none:    cover property (@(A or B or C or D) !ab && !cd && !Y);

  // Toggle coverage
  cover property (@(posedge A) 1); cover property (@(negedge A) 1);
  cover property (@(posedge B) 1); cover property (@(negedge B) 1);
  cover property (@(posedge C) 1); cover property (@(negedge C) 1);
  cover property (@(posedge D) 1); cover property (@(negedge D) 1);
  cover property (@(posedge Y) 1); cover property (@(negedge Y) 1);

endmodule

// Bind to all instances of logic_operation
bind logic_operation logic_operation_sva sva_i (
  .A(A), .B(B), .C(C), .D(D), .Y(Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);