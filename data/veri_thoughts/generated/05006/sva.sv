module binary_adder_sva (
    input logic clk,
    input logic [3:0] addend1,
    input logic [3:0] addend2,
    input logic carry_in,
    input logic [3:0] sum,
    input logic carry_out
);

    // Combined output must match the 5-bit addition result.
    check_full_add_result: assert property (
        @(posedge clk)
        {carry_out, sum} == ({1'b0, addend1} + {1'b0, addend2} + carry_in)
    );

    // sum must equal the low 4 bits of the addition result.
    check_sum_low_bits: assert property (
        @(posedge clk)
        {1'b0, sum} == (({1'b0, addend1} + {1'b0, addend2} + carry_in) & 5'h0F)
    );

    // carry_out must indicate overflow beyond 4 bits.
    check_carry_out_overflow: assert property (
        @(posedge clk)
        carry_out == (({1'b0, addend1} + {1'b0, addend2} + carry_in) > 5'd15)
    );

    // Zero operands with no carry-in must produce zero.
    check_zero_result: assert property (
        @(posedge clk)
        ((addend1 == 4'd0) && (addend2 == 4'd0) && (carry_in == 1'b0)) |-> ({carry_out, sum} == 5'd0)
    );

    // With addend2 cleared and no carry-in, the output must pass through addend1.
    check_addend1_passthrough: assert property (
        @(posedge clk)
        ((addend2 == 4'd0) && (carry_in == 1'b0)) |-> ({carry_out, sum} == {1'b0, addend1})
    );

    // With addend1 cleared and no carry-in, the output must pass through addend2.
    check_addend2_passthrough: assert property (
        @(posedge clk)
        ((addend1 == 4'd0) && (carry_in == 1'b0)) |-> ({carry_out, sum} == {1'b0, addend2})
    );

    // A lone carry-in must increment zero operands to one without overflow.
    check_carry_in_increment: assert property (
        @(posedge clk)
        ((addend1 == 4'd0) && (addend2 == 4'd0) && (carry_in == 1'b1)) |-> ((sum == 4'd1) && (carry_out == 1'b0))
    );

    // Maximum operands with carry-in must overflow and leave sum at 4'hF.
    check_maximum_overflow: assert property (
        @(posedge clk)
        ((addend1 == 4'hF) && (addend2 == 4'hF) && (carry_in == 1'b1)) |-> ((sum == 4'hF) && (carry_out == 1'b1))
    );

endmodule