module add_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM
);

    // SUM[0] matches the RTL XOR of the least-significant input bits.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0])
    );

    // SUM[1] matches the RTL XOR with the bit-0 generate term.
    check_sum_bit1: assert property (
        @(posedge clk) SUM[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // SUM[2] matches the RTL XOR with the OR of lower generate terms.
    check_sum_bit2: assert property (
        @(posedge clk) SUM[2] == ((A[2] ^ B[2]) ^ ((A[1] & B[1]) | (A[0] & B[0])))
    );

    // SUM[3] matches the RTL XOR with the OR of all lower generate terms.
    check_sum_bit3: assert property (
        @(posedge clk) SUM[3] == ((A[3] ^ B[3]) ^ ((A[2] & B[2]) | (A[1] & B[1]) | (A[0] & B[0])))
    );

    // The full SUM bus matches the combined RTL equations.
    check_sum_vector: assert property (
        @(posedge clk) SUM == {
            ((A[3] ^ B[3]) ^ ((A[2] & B[2]) | (A[1] & B[1]) | (A[0] & B[0]))),
            ((A[2] ^ B[2]) ^ ((A[1] & B[1]) | (A[0] & B[0]))),
            ((A[1] ^ B[1]) ^ (A[0] & B[0])),
            (A[0] ^ B[0])
        }
    );

endmodule