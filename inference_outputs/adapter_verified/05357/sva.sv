module AND_32bit_sva (
    input logic        clk,
    input logic [31:0] out,
    input logic [31:0] A,
    input logic [31:0] B
);

// out equals bitwise AND of A and B.
    check_vector_and: assert property (
        @(posedge clk) out == (A & B)
    );

// If A is all zeros, out must be all zeros.
    check_zero_a_implies_zero_out: assert property (
        @(posedge clk) (A == 32'h0) |-> (out == 32'h0)
    );

// If B is all zeros, out must be all zeros.
    check_zero_b_implies_zero_out: assert property (
        @(posedge clk) (B == 32'h0) |-> (out == 32'h0)
    );

// If A is all ones, out must equal B.
    check_all_ones_a_implies_out_eq_b: assert property (
        @(posedge clk) (A == 32'hFFFF_FFFF) |-> (out == B)
    );

// If B is all ones, out must equal A.
    check_all_ones_b_implies_out_eq_a: assert property (
        @(posedge clk) (B == 32'hFFFF_FFFF) |-> (out == A)
    );

// If A equals B, out must equal A (and B).
    check_equal_inputs_implies_equal_out: assert property (
        @(posedge clk) (A == B) |-> (out == A)
    );

// If out is all ones, then A and B must both be all ones.
    check_all_ones_out_implies_all_ones_inputs: assert property (
        @(posedge clk) (out == 32'hFFFF_FFFF) |-> ((A == 32'hFFFF_FFFF) && (B == 32'hFFFF_FFFF))
    );

// If out has a 0 in bit[i], then at least one of A[i] or B[i] must be 0.
    check_zero_out_bit_implies_zero_input_bit: assert property (
        @(posedge clk) (out[i] == 1'b0) |-> ((A[i] == 1'b0) || (B[i] == 1'b0))
    );

// If A[i] is 0, out[i] must be 0.
    check_zero_a_bit_implies_zero_out_bit: assert property (
        @(posedge clk) (A[i] == 1'b0) |-> (out[i] == 1'b0)
    );

// If B[i] is 0, out[i] must be 0.
    check_zero_b_bit_implies_zero_out_bit: assert property (
        @(posedge clk) (B[i] == 1'b0) |-> (out[i] == 1'b0)
    );

// If A[i] is 1, out[i] equals B[i].
    check_one_a_bit_implies_out_eq_b_bit: assert property (
        @(posedge clk) (A[i] == 1'b1) |-> (out[i] == B[i])
    );

// If B[i] is 1, out[i] equals A[i].
    check_one_b_bit_implies_out_eq_a_bit: assert property (
        @(posedge clk) (B[i] == 1'b1) |-> (out[i] == A[i])
    );

endmodule
