module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] S,
    input logic CO,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI
);

// Sum bit 0 matches the full-adder equation.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ CI)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry_out(A[0], B[0], CI))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry_out(A[1], B[1], carry_out(A[0], B[0], CI)))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry_out(A[2], B[2], carry_out(A[1], B[1], carry_out(A[0], B[0], CI))))
    );

// CO matches the carry-out generated from the MSB stage.
    check_carry_out: assert property (
        @(posedge clk) CO == carry_out(A[3], B[3], carry_out(A[2], B[2], carry_out(A[1], B[1], carry_out(A[0], B[0], CI))))
    );

// All-zero inputs produce all-zero outputs.
    check_zero_inputs: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && CI == 1'b0) |-> (S == 4'b0000 && CO == 1'b0)
    );

// Adding zero with CI low passes A through unchanged.
    check_a_passthrough: assert property (
        @(posedge clk) (B == 4'b0000 && CI == 1'b0) |-> (S == A && CO == 1'b0)
    );

// Adding zero with CI low passes B through unchanged.
    check_b_passthrough: assert property (
        @(posedge clk) (A == 4'b0000 && CI == 1'b0) |-> (S == B && CO == 1'b0)
    );

// CI alone increments zero to one with no carry out.
    check_ci_increment: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && CI == 1'b1) |-> (S == 4'b0001 && CO == 1'b0)
    );

// Maximum inputs with CI high produce 31 with carry out.
    check_max_inputs: assert property (
        @(posedge clk) (A == 4'b1111 && B == 4'b1111 && CI == 1'b1) |-> (S == 4'b1111 && CO == 1'b1)
    );

endmodule
