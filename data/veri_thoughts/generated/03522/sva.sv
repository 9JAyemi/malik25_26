module and_or_xor_adder_sva (
    input logic       clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] out
);

    // RTL is combinational; clk is only used to sample assertions.
    // The RTL has no reset.

    // out must equal the XOR of the AND/OR intermediates plus one.
    check_output_equation: assert property (
        @(posedge clk) out == (((in1 & in2) ^ (in1 | in2)) + 8'h01)
    );

    // Equal inputs make the XOR term zero, so out must be one.
    check_equal_inputs_result_one: assert property (
        @(posedge clk) (in1 == in2) |-> (out == 8'h01)
    );

    // If in1 is zero, the logic reduces to in2 plus one.
    check_zero_in1_behavior: assert property (
        @(posedge clk) (in1 == 8'h00) |-> (out == (in2 + 8'h01))
    );

    // If in2 is zero, the logic reduces to in1 plus one.
    check_zero_in2_behavior: assert property (
        @(posedge clk) (in2 == 8'h00) |-> (out == (in1 + 8'h01))
    );

    // Complementary inputs produce 8'hFF before increment, so out wraps to zero.
    check_complementary_inputs_wrap: assert property (
        @(posedge clk) (in1 == ~in2) |-> (out == 8'h00)
    );

endmodule