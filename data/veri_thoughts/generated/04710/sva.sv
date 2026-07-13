module sky130_fd_sc_ms__a22oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y must equal the implemented AND-of-NANDs function.
    check_output_function: assert property (
        @(posedge clk)
        Y == ((~(A2 & A1)) & (~(B2 & B1)))
    );

    // If A1 and A2 are both high, the output must be low.
    check_a_pair_high_forces_y_low: assert property (
        @(posedge clk)
        ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // If B1 and B2 are both high, the output must be low.
    check_b_pair_high_forces_y_low: assert property (
        @(posedge clk)
        ((B1 & B2) == 1'b1) |-> (Y == 1'b0)
    );

    // If neither input pair is simultaneously high, the output must be high.
    check_no_pair_high_forces_y_high: assert property (
        @(posedge clk)
        (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0)) |-> (Y == 1'b1)
    );

    // A high output means the A input pair is not simultaneously high.
    check_y_high_excludes_a_pair_high: assert property (
        @(posedge clk)
        (Y == 1'b1) |-> ((A1 & A2) == 1'b0)
    );

    // A high output means the B input pair is not simultaneously high.
    check_y_high_excludes_b_pair_high: assert property (
        @(posedge clk)
        (Y == 1'b1) |-> ((B1 & B2) == 1'b0)
    );

    // A low output means at least one input pair is simultaneously high.
    check_y_low_requires_some_pair_high: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> (((A1 & A2) == 1'b1) || ((B1 & B2) == 1'b1))
    );

endmodule