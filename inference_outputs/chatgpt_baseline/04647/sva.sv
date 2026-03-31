module subtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);

    // Output matches the 4-bit subtraction of A and B.
    check_subtract_function: assert property (
        @(posedge clk) disable iff (1'b0) Y == (A - B)
    );

    // Adding B back to Y recovers A modulo 16.
    check_add_back_recovers_a: assert property (
        @(posedge clk) disable iff (1'b0) (Y + B) == A
    );

    // Equal operands produce a zero result.
    check_equal_inputs_zero: assert property (
        @(posedge clk) disable iff (1'b0) (A == B) |-> (Y == 4'h0)
    );

    // Subtracting zero passes A through unchanged.
    check_zero_subtrahend_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (B == 4'h0) |-> (Y == A)
    );

    // Zero minus B produces the wrapped 4-bit result.
    check_zero_minuend_wrap: assert property (
        @(posedge clk) disable iff (1'b0) (A == 4'h0) |-> (Y == (4'h0 - B))
    );

endmodule