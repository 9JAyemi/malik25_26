module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum,
    input logic       carry_out
);
    // Sum equals 4-bit addition (truncation of a+b).
    check_sum_is_add: assert property (
        @(posedge clk) sum == (a + b)
    );

    // Carry-out is always zero (a+b is 4-bit wide).
    check_carry_out_zero: assert property (
        @(posedge clk) carry_out == 1'b0
    );

    // {carry_out,sum} equals zero-extended 4-bit addition.
    check_concatenated_result: assert property (
        @(posedge clk) {carry_out, sum} == {1'b0, (a + b)}
    );

    // LSB of sum is XOR of LSBs of inputs.
    check_sum_bit0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // Bit1 of sum equals XOR of inputs' bit1 with carry from bit0.
    check_sum_bit1_full_adder: assert property (
        @(posedge clk) sum[1] == ((a[1] ^ b[1]) ^ (a[0] & b[0]))
    );

    // Outputs remain stable across cycles when inputs are stable.
    check_outputs_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> ($stable(sum) && $stable(carry_out))
    );
endmodule