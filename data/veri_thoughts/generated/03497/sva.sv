module binary_counter_assertions(
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic overflow
);

    // Output is the 4-bit input incremented by one modulo 16.
    check_out_modulo_increment: assert property (
        @(posedge clk) out == (in + 4'b0001)
    );

    // Overflow is asserted exactly when the input is 4'hF.
    check_overflow_matches_max_input: assert property (
        @(posedge clk) overflow == (in == 4'b1111)
    );

    // Maximum input wraps the output to zero and raises overflow.
    check_max_input_wraps: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 4'b0000 && overflow == 1'b1)
    );

    // Non-maximum input does not raise overflow.
    check_non_max_input_no_overflow: assert property (
        @(posedge clk) (in != 4'b1111) |-> (overflow == 1'b0)
    );

    // Non-maximum input increments the output by one.
    check_non_max_input_increments: assert property (
        @(posedge clk) (in != 4'b1111) |-> (out == (in + 4'b0001))
    );

endmodule