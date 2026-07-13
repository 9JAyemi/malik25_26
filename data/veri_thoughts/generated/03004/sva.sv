module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum,
    input logic carry_out
);

    // No RTL clock or reset; sample this combinational logic on $global_clock.

    // sum matches the exact combinational equation implemented in the RTL.
    check_sum_vector_equation: assert property (
        @($global_clock)
        sum == ((A ^ B) ^
                ({1'b0, (A[3] & B[3]), (A[2] & B[2]), (A[1] & B[1])} |
                 {(A[3] & B[3]), (A[2] & B[2]), (A[1] & B[1]), (A[0] & B[0])}))
    );

    // carry_out matches the RTL carry output equation.
    check_carry_out_equation: assert property (
        @($global_clock)
        carry_out == (A[3] & B[3])
    );

    // sum[3] matches xor_out[3] XOR the MSB carry term.
    check_sum_bit3_equation: assert property (
        @($global_clock)
        sum[3] == ((A[3] ^ B[3]) ^ (A[3] & B[3]))
    );

    // sum[2] matches xor_out[2] XOR the RTL OR of adjacent AND terms.
    check_sum_bit2_equation: assert property (
        @($global_clock)
        sum[2] == ((A[2] ^ B[2]) ^ ((A[3] & B[3]) | (A[2] & B[2])))
    );

    // sum[1] matches xor_out[1] XOR the RTL OR of adjacent AND terms.
    check_sum_bit1_equation: assert property (
        @($global_clock)
        sum[1] == ((A[1] ^ B[1]) ^ ((A[2] & B[2]) | (A[1] & B[1])))
    );

    // sum[0] matches xor_out[0] XOR the RTL OR of adjacent AND terms.
    check_sum_bit0_equation: assert property (
        @($global_clock)
        sum[0] == ((A[0] ^ B[0]) ^ ((A[1] & B[1]) | (A[0] & B[0])))
    );

endmodule