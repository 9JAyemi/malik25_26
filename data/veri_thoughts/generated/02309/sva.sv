module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_in,
    input logic [3:0] S,
    input logic C_out
);
    // Local carry chain expressions derived from the RTL full adders
    let c1 = (A[0] & B[0]) | (C_in & (A[0] ^ B[0]));
    let c2 = (A[1] & B[1]) | (c1 & (A[1] ^ B[1]));
    let c3 = (A[2] & B[2]) | (c2 & (A[2] ^ B[2]));

    // Sum and carry match 5-bit arithmetic addition of inputs
    check_overall_sum: assert property (
        @(posedge clk) {C_out, S} == (A + B + C_in)
    );

    // LSB sum bit equals XOR of inputs
    check_s0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Bit1 sum uses ripple carry from bit0
    check_s1_xor: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ c1)
    );

    // Bit2 sum uses ripple carry from bit1
    check_s2_xor: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ c2)
    );

    // Bit3 sum uses ripple carry from bit2
    check_s3_xor: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ c3)
    );

    // Final carry-out equation at MSB
    check_cout_equation: assert property (
        @(posedge clk) C_out == ((A[3] & B[3]) | (c3 & (A[3] ^ B[3])))
    );

    // If both MSB inputs are 1, carry-out must be 1
    check_cout_msb_both_one: assert property (
        @(posedge clk) (~(A[3] & B[3])) || (C_out == 1'b1)
    );

    // If both MSB inputs are 0, carry-out must be 0
    check_cout_msb_both_zero: assert property (
        @(posedge clk) (~(~A[3] & ~B[3])) || (C_out == 1'b0)
    );

    // If MSB inputs differ, carry-out equals c3
    check_cout_msb_diff_equals_c3: assert property (
        @(posedge clk) (~(A[3] ^ B[3])) || (C_out == c3)
    );

    // If MSB inputs are equal, S[3] equals c3
    check_s3_when_msb_equal: assert property (
        @(posedge clk) (A[3] ^ B[3]) || (S[3] == c3)
    );

    // If MSB inputs differ, S[3] is the inverse of c3
    check_s3_when_msb_diff: assert property (
        @(posedge clk) (~(A[3] ^ B[3])) || (S[3] == ~c3)
    );

    // With A=0 and B=0, S mirrors C_in on bit0 and C_out is 0
    check_zero_inputs_behavior: assert property (
        @(posedge clk) (~((A == 4'd0) && (B == 4'd0))) || ((S == {3'b000, C_in}) && (C_out == 1'b0))
    );

    // With A=15, B=15, C_in=0, result is 30 -> C_out=1, S=14
    check_all_ones_no_cin: assert property (
        @(posedge clk) (~((A == 4'hF) && (B == 4'hF) && (C_in == 1'b0))) || ((S == 4'he) && (C_out == 1'b1))
    );

    // With A=15, B=15, C_in=1, result is 31 -> C_out=1, S=15
    check_all_ones_with_cin: assert property (
        @(posedge clk) (~((A == 4'hF) && (B == 4'hF) && (C_in == 1'b1))) || ((S == 4'hf) && (C_out == 1'b1))
    );

    // If bit0 generates a carry (A0&B0), bit1 sum must invert A1^B1
    check_s1_when_carry_generated_at_bit0: assert property (
        @(posedge clk) (~(A[0] & B[0])) || (S[1] == (A[1] ^ B[1] ^ 1'b1))
    );

endmodule