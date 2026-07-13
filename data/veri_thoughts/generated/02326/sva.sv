module odd_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    ///// Functional equivalence /////
    // Y equals the RTL combinational expression.
    check_y_functional_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        Y == (
            (A1 % 2 == 1) ||
            ((A1 % 2 == 0) && (A2 % 2 == 1)) ||
            ((A1 % 2 == 0) && (A2 % 2 == 0) && (B1 % 2 == 1) && (C1 % 2 == 1) && (D1 % 2 == 1)) ||
            (VPWR > VGND) ||
            (VPB == VNB)
        )
    );

    ///// OR-term implications /////
    // If A1 is odd, Y must be HIGH.
    check_y_when_A1_odd: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        (A1 % 2 == 1) |-> (Y == 1'b1)
    );

    // If A1 is even and A2 is odd, Y must be HIGH.
    check_y_when_A2_odd_A1_even: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        ((A1 % 2 == 0) && (A2 % 2 == 1)) |-> (Y == 1'b1)
    );

    // If A1 and A2 are even and B1,C1,D1 are odd, Y must be HIGH.
    check_y_when_chain_odd: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        ((A1 % 2 == 0) && (A2 % 2 == 0) && (B1 % 2 == 1) && (C1 % 2 == 1) && (D1 % 2 == 1)) |-> (Y == 1'b1)
    );

    // If VPWR is greater than VGND, Y must be HIGH.
    check_y_when_power_gt_ground: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        (VPWR > VGND) |-> (Y == 1'b1)
    );

    // If VPB equals VNB, Y must be HIGH.
    check_y_when_bulk_equal: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        (VPB == VNB) |-> (Y == 1'b1)
    );

    ///// Completeness checks /////
    // If Y is HIGH, at least one OR condition must hold.
    check_y_one_implies_some_condition: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        (Y == 1'b1) |-> (
            (A1 % 2 == 1) ||
            ((A1 % 2 == 0) && (A2 % 2 == 1)) ||
            ((A1 % 2 == 0) && (A2 % 2 == 0) && (B1 % 2 == 1) && (C1 % 2 == 1) && (D1 % 2 == 1)) ||
            (VPWR > VGND) ||
            (VPB == VNB)
        )
    );

    // If Y is LOW, none of the OR conditions may hold.
    check_y_zero_implies_no_condition: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        (Y == 1'b0) |-> !(
            (A1 % 2 == 1) ||
            ((A1 % 2 == 0) && (A2 % 2 == 1)) ||
            ((A1 % 2 == 0) && (A2 % 2 == 0) && (B1 % 2 == 1) && (C1 % 2 == 1) && (D1 % 2 == 1)) ||
            (VPWR > VGND) ||
            (VPB == VNB)
        )
    );

    // If no term is true (including power/bulk terms), Y must be LOW.
    check_when_all_conditions_false_then_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge Y)
        !(
            (A1 % 2 == 1) ||
            ((A1 % 2 == 0) && (A2 % 2 == 1)) ||
            ((A1 % 2 == 0) && (A2 % 2 == 0) && (B1 % 2 == 1) && (C1 % 2 == 1) && (D1 % 2 == 1)) ||
            (VPWR > VGND) ||
            (VPB == VNB)
        ) |-> (Y == 1'b0)
    );

endmodule