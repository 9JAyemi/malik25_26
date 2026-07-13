module adder_16bit_sva (
    input logic clk,
    input logic [15:0] operand1,
    input logic [15:0] operand2,
    input logic carry_in,
    input logic [15:0] sum,
    input logic carry_out
);

    // Full output must match the 17-bit addition of the inputs.
    check_full_add_result: assert property (
        @(posedge clk)
        {carry_out, sum} == ({1'b0, operand1} + {1'b0, operand2} + {16'b0, carry_in})
    );

    // sum must equal the lower 16 bits of the addition result.
    check_sum_lower_bits: assert property (
        @(posedge clk)
        {1'b0, sum} == (({1'b0, operand1} + {1'b0, operand2} + {16'b0, carry_in}) & 17'h0_FFFF)
    );

    // carry_out must equal the overflow bit of the addition result.
    check_carry_out_overflow: assert property (
        @(posedge clk)
        carry_out == (({1'b0, operand1} + {1'b0, operand2} + {16'b0, carry_in}) > 17'h0_FFFF)
    );

endmodule