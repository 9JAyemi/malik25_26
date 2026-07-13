module AND_32bit_sva (
    input logic CLK,
    input logic [31:0] out,
    input logic [31:0] A,
    input logic [31:0] B
);
    // out equals bitwise AND of A and B.
    check_out_equals_and: assert property (
        @(posedge CLK) out == (A & B)
    );

    // out[i] equals A[i] & B[i] for each bit i.
    check_bitwise_and: assert property (
        @(posedge CLK) out[i] == (A[i] & B[i]) for (genvar i = 0; i < 32; i++)
    );

    // If A[i] is 0, out[i] must be 0.
    check_zero_when_A_zero: assert property (
        @(posedge CLK) (A[i] == 1'b0) |-> (out[i] == 1'b0) for (genvar i = 0; i < 32; i++)
    );

    // If B[i] is 0, out[i] must be 0.
    check_zero_when_B_zero: assert property (
        @(posedge CLK) (B[i] == 1'b0) |-> (out[i] == 1'b0) for (genvar i = 0; i < 32; i++)
    );

    // If A[i] is 1, out[i] equals B[i].
    check_pass_through_when_A_one: assert property (
        @(posedge CLK) (A[i] == 1'b1) |-> (out[i] == B[i]) for (genvar i = 0; i < 32; i++)
    );

    // If B[i] is 1, out[i] equals A[i].
    check_pass_through_when_B_one: assert property (
        @(posedge CLK) (B[i] == 1'b1) |-> (out[i] == A[i]) for (genvar i = 0; i < 32; i++)
    );

    // If A and B are equal, out equals A (and B).
    check_equal_inputs: assert property (
        @(posedge CLK) (A == B) |-> (out == A)
    );

    // If A is all ones, out equals B.
    check_all_ones_A: assert property (
        @(posedge CLK) (A == 32'hFFFF_FFFF) |-> (out == B)
    );

    // If B is all ones, out equals A.
    check_all_ones_B: assert property (
        @(posedge CLK) (B == 32'hFFFF_FFFF) |-> (out == A)
    );

    // If A is all zeros, out is all zeros.
    check_all_zeros_A: assert property (
        @(posedge CLK) (A == 32'h0000_0000) |-> (out == 32'h0000_0000)
    );

    // If B is all zeros, out is all zeros.
    check_all_zeros_B: assert property (
        @(posedge CLK) (B == 32'h0000_0000) |-> (out == 32'h0000_0000)
    );

    // If A is all ones and B is all ones, out is all ones.
    check_all_ones_inputs: assert property (
        @(posedge CLK) ((A == 32'hFFFF_FFFF) && (B == 32'hFFFF_FFFF)) |-> (out == 32'hFFFF_FFFF)
    );

    // If A is all zeros and B is all zeros, out is all zeros.
    check_all_zeros_inputs: assert property (
        @(posedge CLK) ((A == 32'h0000_0000) && (B == 32'h0000_0000)) |-> (out == 32'h0000_0000)
    );

    // If A is all ones and B is all zeros, out is all zeros.
    check_all_ones_A_all_zeros_B: assert property (
        @(posedge CLK) ((A == 32'hFFFF_FFFF) && (B == 32'h0000_0000)) |-> (out == 32'h0000_0000)
    );

    // If A is all zeros and B is all ones, out is all zeros.
    check_all_zeros_A_all_ones_B: assert property (
        @(posedge CLK) ((A == 32'h0000_0000) && (B == 32'hFFFF_FFFF)) |-> (out == 32'h0000_0000)
    );
endmodule