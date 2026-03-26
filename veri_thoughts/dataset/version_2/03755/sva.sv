module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] sum_and_carry
);

    // Output matches the masked 9-bit addition implemented by the RTL.
    check_output_matches_masked_add: assert property (
        @(posedge clk) disable iff (reset)
        sum_and_carry == (({1'b0, a} + {1'b0, b}) & {1'b1, (a & b)})
    );

    // Carry bit matches the carry-out of the 8-bit addition.
    check_carry_matches_addition: assert property (
        @(posedge clk) disable iff (reset)
        sum_and_carry[8] == (({1'b0, a} + {1'b0, b}) > 9'h0ff)
    );

    // Low byte equals the bitwise-AND result masked by the adder sum.
    check_low_byte_matches_and_of_sum: assert property (
        @(posedge clk) disable iff (reset)
        sum_and_carry[7:0] == ((a & b) & (a + b))
    );

    // Low byte can only set bits that are set in both inputs.
    check_low_byte_subset_of_input_and: assert property (
        @(posedge clk) disable iff (reset)
        (sum_and_carry[7:0] & ~(a & b)) == 8'h00
    );

    // If either operand is zero, the combined output is zero.
    check_zero_operand_gives_zero_output: assert property (
        @(posedge clk) disable iff (reset)
        ((a == 8'h00) || (b == 8'h00)) |-> (sum_and_carry == 9'h000)
    );

    // All-ones operands produce carry with a low byte of 8'hfe.
    check_all_ones_corner_case: assert property (
        @(posedge clk) disable iff (reset)
        ((a == 8'hff) && (b == 8'hff)) |-> (sum_and_carry == 9'h1fe)
    );

endmodule