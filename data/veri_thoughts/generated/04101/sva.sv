module multiplier_sva (
    input logic       clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [7:0] out
);

    // Output matches 4x4 arithmetic multiplication.
    check_product_matches_multiply: assert property (
        @(posedge clk) out == (in1 * in2)
    );

    // Output equals the sum of shifted partial products.
    check_shift_add_decomposition: assert property (
        @(posedge clk)
        out == ((in1[0] ? {4'b0000, in2} : 8'h00) +
                (in1[1] ? ({4'b0000, in2} << 1) : 8'h00) +
                (in1[2] ? ({4'b0000, in2} << 2) : 8'h00) +
                (in1[3] ? ({4'b0000, in2} << 3) : 8'h00))
    );

    // Bit 0 is the direct LSB partial product.
    check_lsb_partial_product: assert property (
        @(posedge clk) out[0] == (in1[0] & in2[0])
    );

    // Bit 1 is the XOR of the first two cross products.
    check_bit1_partial_sum: assert property (
        @(posedge clk) out[1] == ((in1[1] & in2[0]) ^ (in1[0] & in2[1]))
    );

    // Bit 2 includes the carry generated from bit 1 accumulation.
    check_bit2_partial_sum: assert property (
        @(posedge clk)
        out[2] == ((in1[2] & in2[0]) ^
                   (in1[1] & in2[1]) ^
                   (in1[0] & in2[2]) ^
                   ((in1[1] & in2[0]) & (in1[0] & in2[1])))
    );

    // A zero multiplicand produces a zero result.
    check_zero_when_in1_zero: assert property (
        @(posedge clk) (in1 == 4'h0) |-> (out == 8'h00)
    );

    // A zero multiplier produces a zero result.
    check_zero_when_in2_zero: assert property (
        @(posedge clk) (in2 == 4'h0) |-> (out == 8'h00)
    );

    // Multiplying by one passes through the second operand.
    check_identity_when_in1_one: assert property (
        @(posedge clk) (in1 == 4'h1) |-> (out == {4'b0000, in2})
    );

    // Multiplying by one passes through the first operand.
    check_identity_when_in2_one: assert property (
        @(posedge clk) (in2 == 4'h1) |-> (out == {4'b0000, in1})
    );

    // Multiplying by 8 shifts the second operand left by three.
    check_shift_by_msb_in1: assert property (
        @(posedge clk) (in1 == 4'h8) |-> (out == ({4'b0000, in2} << 3))
    );

    // Multiplying by 8 shifts the first operand left by three.
    check_shift_by_msb_in2: assert property (
        @(posedge clk) (in2 == 4'h8) |-> (out == ({4'b0000, in1} << 3))
    );

endmodule