module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic [3:0] SUM,
    input logic COUT
);

    // External sampling clock; RTL has no clock or reset.

    // SUM must match the implemented bitwise XOR with replicated CI.
    check_sum_vector: assert property (
        @(posedge clk) SUM == (A ^ B ^ {4{CI}})
    );

    // SUM[0] is A[0] xor B[0] xor CI.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0] ^ CI)
    );

    // SUM[1] is A[1] xor B[1] xor CI.
    check_sum_bit1: assert property (
        @(posedge clk) SUM[1] == (A[1] ^ B[1] ^ CI)
    );

    // SUM[2] is A[2] xor B[2] xor CI.
    check_sum_bit2: assert property (
        @(posedge clk) SUM[2] == (A[2] ^ B[2] ^ CI)
    );

    // SUM[3] is A[3] xor B[3] xor CI.
    check_sum_bit3: assert property (
        @(posedge clk) SUM[3] == (A[3] ^ B[3] ^ CI)
    );

    // COUT must match the implemented relation to SUM[3].
    check_cout_from_sum_msb: assert property (
        @(posedge clk) COUT == (SUM[3] ^ (A[3] & B[3] & CI))
    );

    // COUT must match the exact implemented MSB equation.
    check_cout_function: assert property (
        @(posedge clk) COUT == (A[3] ^ B[3] ^ CI ^ (A[3] & B[3] & CI))
    );

    // With CI low, SUM reduces to A xor B.
    check_sum_ci_low: assert property (
        @(posedge clk) (!CI) |-> (SUM == (A ^ B))
    );

    // With CI high, SUM reduces to bitwise complement of A xor B.
    check_sum_ci_high: assert property (
        @(posedge clk) CI |-> (SUM == ~(A ^ B))
    );

    // With CI low, COUT reduces to the MSB xor.
    check_cout_ci_low: assert property (
        @(posedge clk) (!CI) |-> (COUT == (A[3] ^ B[3]))
    );

    // With CI high, COUT is high only when both MSB inputs are low.
    check_cout_ci_high: assert property (
        @(posedge clk) CI |-> (COUT == ~(A[3] | B[3]))
    );

endmodule