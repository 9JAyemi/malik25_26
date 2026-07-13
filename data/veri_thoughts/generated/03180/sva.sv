module byte_sum_and_multiply_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [15:0] out,
    input logic [7:0]  upper_byte,
    input logic [7:0]  lower_byte,
    input logic [15:0] sum
);

    // No clock or reset exists in the DUT; clk is the assertion sampling clock.

    // upper_byte must mirror the upper input byte.
    check_upper_byte_extract: assert property (
        @(posedge clk)
        upper_byte == in[15:8]
    );

    // lower_byte must mirror the lower input byte.
    check_lower_byte_extract: assert property (
        @(posedge clk)
        lower_byte == in[7:0]
    );

    // sum must be the zero-extended 8-bit addition of the two bytes.
    check_sum_zero_extended_byte_add: assert property (
        @(posedge clk)
        sum == {8'h00, (upper_byte + lower_byte)}
    );

    // out must be twice sum.
    check_out_is_double_sum: assert property (
        @(posedge clk)
        out == (sum << 1)
    );

    // out must match the end-to-end byte-add-then-double function.
    check_end_to_end_function: assert property (
        @(posedge clk)
        out == ({8'h00, (in[15:8] + in[7:0])} << 1)
    );

    // out is always even because the computed sum is doubled.
    check_out_is_even: assert property (
        @(posedge clk)
        out[0] == 1'b0
    );

    // out cannot exceed the doubled maximum 8-bit sum.
    check_out_range: assert property (
        @(posedge clk)
        out <= 16'h01FE
    );

    // Zero input must produce zero output.
    check_zero_input_zero_output: assert property (
        @(posedge clk)
        (in == 16'h0000) |-> (out == 16'h0000)
    );

    // All-ones input must reflect 8-bit addition truncation before doubling.
    check_all_ones_input_output: assert property (
        @(posedge clk)
        (in == 16'hFFFF) |-> (out == 16'h01FC)
    );

    // 8'hFF plus 8'h01 wraps in 8-bit addition, producing zero output.
    check_byte_add_wrap_example: assert property (
        @(posedge clk)
        (in == 16'hFF01) |-> (out == 16'h0000)
    );

endmodule