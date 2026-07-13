module and_or_buf_sva (
    input logic clk,
    input logic [2:0] A,
    input logic B,
    input logic X
);

    // X must equal the OR of A bits gated by B.
    check_output_matches_logic: assert property (
        @(posedge clk) X == ((A[2] | A[1] | A[0]) & B)
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // All A bits low forces X low.
    check_a_zero_forces_x_low: assert property (
        @(posedge clk) (A == 3'b000) |-> !X
    );

    // B high with any A bit high forces X high.
    check_b_high_and_any_a_high_forces_x_high: assert property (
        @(posedge clk) (B && (|A)) |-> X
    );

    // X high requires B high and at least one A bit high.
    check_x_high_requires_b_and_any_a_high: assert property (
        @(posedge clk) X |-> (B && (|A))
    );

endmodule