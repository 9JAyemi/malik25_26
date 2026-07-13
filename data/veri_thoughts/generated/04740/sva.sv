module sky130_fd_sc_lp__o21ai_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic VDD,
    input logic VSS
);

    // No RTL clock/reset; sample this combinational cell on clk.
    // Y matches the implemented combinational equation.
    check_function_equation: assert property (
        @(posedge clk) Y == ((A1 | A2) | ~B1)
    );

    // A1 high forces Y high.
    check_a1_high_forces_y_high: assert property (
        @(posedge clk) (A1 == 1'b1) |-> (Y == 1'b1)
    );

    // A2 high forces Y high.
    check_a2_high_forces_y_high: assert property (
        @(posedge clk) (A2 == 1'b1) |-> (Y == 1'b1)
    );

    // B1 low forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A1=0, A2=0, B1=1 drives Y low.
    check_blocking_case_drives_y_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // If Y is low, inputs match the only low-output case.
    check_y_low_implies_blocking_case: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b1))
    );

    // Stable sampled inputs keep the sampled output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({A1, A2, B1}) |-> $stable(Y)
    );

endmodule