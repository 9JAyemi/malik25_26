module Adder4bit_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [3:0]  S,
    input logic        Co
);

// Sum bit 0 matches the full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b0)))
    );

// Sum bit 2 uses the ripple carry from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b0)))))
    );

// Sum bit 3 uses the ripple carry from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b0)))))))
    );

// Carry-out matches the final ripple carry stage.
    check_carry_out: assert property (
        @(posedge clk) Co == ((A[3] & B[3]) | ((A[3] ^ B[3]) & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b0))))))))
    );

// Zero plus zero produces zero with no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000) |-> (S == 4'b0000 && Co == 1'b0)
    );

// Adding zero on B passes A through with no carry.
    check_add_zero_on_b: assert property (
        @(posedge clk) (B == 4'b0000) |-> (S == A && Co == 1'b0)
    );

// Adding zero on A passes B through with no carry.
    check_add_zero_on_a: assert property (
        @(posedge clk) (A == 4'b0000) |-> (S == B && Co == 1'b0)
    );

// Maximum inputs produce all ones with carry-out.
    check_max_plus_max: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF) |-> (S == 4'hF && Co == 1'b1)
    );

endmodule
