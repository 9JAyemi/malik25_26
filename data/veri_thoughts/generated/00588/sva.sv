module sky130_fd_sc_hvl__nand3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // When all inputs are 1, Y must be 0 (NAND3 truth).
    check_all_ones_drives_low: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1 && C == 1'b1) |-> (Y == 1'b0)
    );

    // If A is 0, Y must be 1 (NAND3 truth).
    check_a_zero_forces_high: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b1)
    );

    // If B is 0, Y must be 1 (NAND3 truth).
    check_b_zero_forces_high: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b1)
    );

    // If C is 0, Y must be 1 (NAND3 truth).
    check_c_zero_forces_high: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b1)
    );

    // Y can be 0 only when A, B, and C are all 1.
    check_only_low_if_all_ones: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A == 1'b1 && B == 1'b1 && C == 1'b1)
    );

    // If Y is 1, not all inputs are 1.
    check_high_implies_not_all_ones: assert property (
        @(posedge clk) (Y == 1'b1) |-> !((A == 1'b1) && (B == 1'b1) && (C == 1'b1))
    );

    // If inputs are stable across a cycle, Y must also be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Y)
    );

    // A falling edge on Y implies all inputs are 1 now.
    check_y_fall_requires_all_ones: assert property (
        @(posedge clk) $fell(Y) |-> (A == 1'b1 && B == 1'b1 && C == 1'b1)
    );

    // A rising edge on Y implies at least one input is 0 now.
    check_y_rise_requires_any_zero: assert property (
        @(posedge clk) $rose(Y) |-> (A == 1'b0 || B == 1'b0 || C == 1'b0)
    );
endmodule