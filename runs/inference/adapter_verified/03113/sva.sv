module addition_module_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum,
    input logic carry
);

// sum[7:0] equals A + B (8-bit wrap).
    check_sum_low_byte: assert property (
        @(posedge clk) sum[7:0] == (A + B)
    );

// sum[8] equals A[7] & B[7] (carry-out from bit 7).
    check_sum_msb_carry: assert property (
        @(posedge clk) sum[8] == (A[7] & B[7])
    );

// carry equals A[7] & B[7] (carry-out from bit 7).
    check_carry_definition: assert property (
        @(posedge clk) carry == (A[7] & B[7])
    );

// sum equals {carry, A + B} (8-bit plus 1-bit).
    check_sum_vector: assert property (
        @(posedge clk) sum == {carry, (A + B)}
    );

// When A + B < 256, carry is 0 and sum equals A + B.
    check_no_carry_case: assert property (
        @(posedge clk) (A + B) < 8'h100 |-> (carry == 1'b0 && sum == (A + B))
    );

// When A + B == 256, carry is 1 and sum is 0.
    check_carry_case: assert property (
        @(posedge clk) (A + B) == 8'h100 |-> (carry == 1'b1 && sum == 8'h00)
    );

// When A + B > 256, carry is 1 and sum equals (A + B) - 256.
    check_overflow_case: assert property (
        @(posedge clk) (A + B) > 8'h100 |-> (carry == 1'b1 && sum == ((A + B) - 8'h100))
    );

// If A is 0, sum equals B and carry is 0.
    check_zero_a_case: assert property (
        @(posedge clk) (A == 8'h00) |-> (sum == B && carry == 1'b0)
    );

// If B is 0, sum equals A and carry is 0.
    check_zero_b_case: assert property (
        @(posedge clk) (B == 8'h00) |-> (sum == A && carry == 1'b0)
    );

endmodule
