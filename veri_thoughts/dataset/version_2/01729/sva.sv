module sum_4bit_sva (
    input logic clk,
    input logic [3:0] input_a,
    input logic [4:0] output_sum
);
    // Output is zero-extended input_a plus 1.
    check_sum_functional: assert property (
        @(posedge clk) output_sum == ({1'b0, input_a} + 5'd1)
    );

    // Lower 4 bits equal input_a + 1 modulo 16.
    check_lower_nibble_increment: assert property (
        @(posedge clk) output_sum[3:0] == (input_a + 4'd1)
    );

    // Carry-out equals reduction AND of input_a (overflow on 0xF).
    check_carry_out_condition: assert property (
        @(posedge clk) output_sum[4] == (&input_a)
    );

    // LSB toggles on +1 increment.
    check_bit0_toggle: assert property (
        @(posedge clk) output_sum[0] == ~input_a[0]
    );

    // Bit1 equals a1 XOR a0 for +1 increment.
    check_bit1_logic: assert property (
        @(posedge clk) output_sum[1] == (input_a[1] ^ input_a[0])
    );

    // Bit2 equals a2 XOR (a1 & a0) for +1 increment.
    check_bit2_logic: assert property (
        @(posedge clk) output_sum[2] == (input_a[2] ^ (input_a[1] & input_a[0]))
    );

    // Bit3 equals a3 XOR (a2 & a1 & a0) for +1 increment.
    check_bit3_logic: assert property (
        @(posedge clk) output_sum[3] == (input_a[3] ^ (input_a[2] & input_a[1] & input_a[0]))
    );

    // When input is 0xF, sum is 0x10.
    check_overflow_case: assert property (
        @(posedge clk) (input_a == 4'hF) |-> (output_sum == 5'h10)
    );

    // When input is 0x0, sum is 0x01.
    check_zero_input_case: assert property (
        @(posedge clk) (input_a == 4'h0) |-> (output_sum == 5'h01)
    );

    // If input_a is unchanged across cycles, output_sum is unchanged.
    check_functional_stability: assert property (
        @(posedge clk) (input_a == $past(input_a)) |-> (output_sum == $past(output_sum))
    );
endmodule