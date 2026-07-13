module my_module_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Y must always be driven to either VPWR or VGND.
    check_y_within_power_rails: assert property (
        @(posedge VPWR) (Y == VPWR) || (Y == VGND)
    );

    // Y matches the RTL combinational definition selecting VPWR/VGND.
    check_y_matches_rtl_condition: assert property (
        @(posedge VPWR)
            Y == ( (((A & B) & C) | ((A & C) & ~B) | ((B & C) & ~A) | (~(A & B) & ~(A & C) & ~(B & C))) ? VPWR : VGND )
    );

    // If no two inputs are HIGH, Y must be VPWR.
    check_y_vpwr_when_no_two_high: assert property (
        @(posedge VPWR) (~(A & B) && ~(A & C) && ~(B & C)) |-> (Y == VPWR)
    );

    // If A and C are HIGH, Y must be VPWR (independent of B).
    check_y_vpwr_when_a_and_c: assert property (
        @(posedge VPWR) (A && C) |-> (Y == VPWR)
    );

    // If B and C are HIGH and A is LOW, Y must be VPWR.
    check_y_vpwr_when_b_and_c_no_a: assert property (
        @(posedge VPWR) (B && C && !A) |-> (Y == VPWR)
    );

    // If A and B are HIGH and C is LOW, Y must be VGND.
    check_y_vgnd_when_a_and_b_no_c: assert property (
        @(posedge VPWR) (A && B && !C) |-> (Y == VGND)
    );

    // If all inputs are LOW, Y must be VPWR.
    check_y_vpwr_when_all_zero: assert property (
        @(posedge VPWR) (!A && !B && !C) |-> (Y == VPWR)
    );

    // If all inputs are HIGH, Y must be VPWR.
    check_y_vpwr_when_all_one: assert property (
        @(posedge VPWR) (A && B && C) |-> (Y == VPWR)
    );

    // If A is LOW and C is HIGH, Y must be VPWR (independent of B).
    check_y_vpwr_when_a0_c1: assert property (
        @(posedge VPWR) (!A && C) |-> (Y == VPWR)
    );

    // If VPWR equals VGND, Y must equal that common value.
    check_y_equal_rail_when_rails_equal: assert property (
        @(posedge VPWR) (VPWR == VGND) |-> (Y == VPWR)
    );
endmodule