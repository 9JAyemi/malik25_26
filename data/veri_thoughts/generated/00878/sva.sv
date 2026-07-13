module sky130_fd_sc_ls__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Y implements ~( (A1 & A2) | B1 | C1 )
    check_functional_equation: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~((A1 & A2) | B1 | C1)
    );

    // If B1 is HIGH, Y must be LOW.
    check_B1_high_forces_Y0: assert property (
        @(posedge clk) disable iff (1'b0) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // If C1 is HIGH, Y must be LOW.
    check_C1_high_forces_Y0: assert property (
        @(posedge clk) disable iff (1'b0) (C1 == 1'b1) |-> (Y == 1'b0)
    );

    // If both A1 and A2 are HIGH, Y must be LOW.
    check_A1A2_both_high_forces_Y0: assert property (
        @(posedge clk) disable iff (1'b0) (A1 && A2) |-> (Y == 1'b0)
    );

    // If B1 and C1 are LOW and (A1 & A2)==0, Y must be HIGH.
    check_no_blockers_and_and_is_zero_gives_Y1: assert property (
        @(posedge clk) disable iff (1'b0) (!B1 && !C1 && !(A1 && A2)) |-> (Y == 1'b1)
    );

    // If all inputs are LOW, Y must be HIGH.
    check_all_inputs_low_gives_Y1: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !A2 && !B1 && !C1) |-> (Y == 1'b1)
    );

    // If Y is HIGH, then B1==0, C1==0, and not(A1 & A2).
    check_Y1_implies_inputs_restricted: assert property (
        @(posedge clk) disable iff (1'b0) (Y == 1'b1) |-> (!B1 && !C1 && !(A1 && A2))
    );

    // If Y is LOW, then (A1 & A2) or B1 or C1 must be HIGH.
    check_Y0_implies_some_input_active: assert property (
        @(posedge clk) disable iff (1'b0) (Y == 1'b0) |-> ((A1 && A2) || B1 || C1)
    );

    // With no blockers (B1=C1=0) and A1=1, Y equals ~A2.
    check_no_blockers_A1_controls_Y: assert property (
        @(posedge clk) disable iff (1'b0) (A1 && !B1 && !C1) |-> (Y == ~A2)
    );

    // With no blockers (B1=C1=0) and A2=1, Y equals ~A1.
    check_no_blockers_A2_controls_Y: assert property (
        @(posedge clk) disable iff (1'b0) (A2 && !B1 && !C1) |-> (Y == ~A1)
    );
endmodule