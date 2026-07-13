module sky130_fd_sc_hd__nand3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Y implements a 3-input NAND of A,B,C.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A & B & C)
    );

    // When all inputs are HIGH, Y must be LOW.
    check_all_high_drives_low: assert property (
        @(posedge clk) (A && B && C) |-> (Y == 1'b0)
    );

    // Y LOW implies all inputs are HIGH.
    check_low_implies_all_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A && B && C)
    );

    // If A is LOW, Y must be HIGH (regardless of B and C).
    check_any_low_A_drives_high: assert property (
        @(posedge clk) (!A) |-> (Y == 1'b1)
    );

    // If B is LOW, Y must be HIGH (regardless of A and C).
    check_any_low_B_drives_high: assert property (
        @(posedge clk) (!B) |-> (Y == 1'b1)
    );

    // If C is LOW, Y must be HIGH (regardless of A and B).
    check_any_low_C_drives_high: assert property (
        @(posedge clk) (!C) |-> (Y == 1'b1)
    );

    // If A rises while B and C are HIGH, Y must be LOW.
    check_rise_A_with_BC_high_drives_low: assert property (
        @(posedge clk) ($rose(A) && B && C) |-> (Y == 1'b0)
    );

    // If A falls while B and C are HIGH, Y must be HIGH.
    check_fall_A_with_BC_high_drives_high: assert property (
        @(posedge clk) ($fell(A) && B && C) |-> (Y == 1'b1)
    );

    // If B rises while A and C are HIGH, Y must be LOW.
    check_rise_B_with_AC_high_drives_low: assert property (
        @(posedge clk) ($rose(B) && A && C) |-> (Y == 1'b0)
    );

    // If C rises while A and B are HIGH, Y must be LOW.
    check_rise_C_with_AB_high_drives_low: assert property (
        @(posedge clk) ($rose(C) && A && B) |-> (Y == 1'b0)
    );

    // If inputs are stable, output must be stable (pure combinational).
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Y)
    );
endmodule