module sky130_fd_sc_ms__nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y matches the implemented NOT-OR function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == (A_N | ~B)
    );

    // A_N high forces the OR term high and drives Y high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B low forces the inverted B term high and drives Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // With both inputs inactive, Y must be low.
    check_both_inputs_inactive_drive_y_low: assert property (
        @(posedge clk) (!A_N && B) |-> !Y
    );

    // A low Y can only occur when A_N is low and B is high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) !Y |-> (!A_N && B)
    );

endmodule