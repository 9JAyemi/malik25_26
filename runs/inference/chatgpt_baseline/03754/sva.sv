module sky130_fd_sc_ms__nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y matches the implemented gate equation.
    check_boolean_function: assert property (
        @(posedge clk) Y == (A_N | ~B)
    );

    // A_N high forces Y high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B low forces Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b1)
    );

    // The only low-output case is A_N low with B high.
    check_low_output_case: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y implies A_N is low and B is high.
    check_y_low_implies_inputs: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A_N == 1'b0) && (B == 1'b1))
    );

endmodule