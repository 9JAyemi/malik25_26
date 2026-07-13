module top_module_sva (
    input logic [3:0] binary_input,
    input logic [1:0] shift_amount,
    input logic [3:0] shifted_gray_code_output
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Shift amount 0 passes the Gray-code input through unchanged.
    check_shift0_passthrough: assert property (
        @($global_clock)
        (shift_amount == 2'b00) |-> (shifted_gray_code_output == {binary_input[3], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Shift amount 1 rotates the Gray-code input left by one bit.
    check_shift1_rotate_left: assert property (
        @($global_clock)
        (shift_amount == 2'b01) |-> (shifted_gray_code_output == {binary_input[2], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Shift amount 2 rotates the Gray-code input left by two bits.
    check_shift2_rotate_left: assert property (
        @($global_clock)
        (shift_amount == 2'b10) |-> (shifted_gray_code_output == {binary_input[1], binary_input[2], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1]})
    );

    // Shift amount 3 rotates the Gray-code input left by three bits.
    check_shift3_rotate_left: assert property (
        @($global_clock)
        (shift_amount == 2'b11) |-> (shifted_gray_code_output == {binary_input[0], binary_input[1], binary_input[2], binary_input[3] ^ binary_input[2]})
    );

    // The MSB is always the original MSB.
    check_msb_preserved: assert property (
        @($global_clock)
        shifted_gray_code_output[3] == binary_input[3]
    );

    // Shift amount 0 preserves the Gray-code bit mapping.
    check_shift0_gray_mapping: assert property (
        @($global_clock)
        (shift_amount == 2'b00) |-> (shifted_gray_code_output[2] == (binary_input[3] ^ binary_input[2])) &&
                                   (shifted_gray_code_output[1] == (binary_input[2] ^ binary_input[1])) &&
                                   (shifted_gray_code_output[0] == (binary_input[1] ^ binary_input[0]))
    );

    // Shift amount 1 preserves the Gray-code bit mapping.
    check_shift1_gray_mapping: assert property (
        @($global_clock)
        (shift_amount == 2'b01) |-> (shifted_gray_code_output[2] == (binary_input[2] ^ binary_input[1])) &&
                                   (shifted_gray_code_output[1] == (binary_input[1] ^ binary_input[0])) &&
                                   (shifted_gray_code_output[0] == (binary_input[0] ^ binary_input[3]))
    );

    // Shift amount 2 preserves the Gray-code bit mapping.
    check_shift2_gray_mapping: assert property (
        @($global_clock)
        (shift_amount == 2'b10) |-> (shifted_gray_code_output[2] == (binary_input[1] ^ binary_input[0])) &&
                                   (shifted_gray_code_output[1] == (binary_input[0] ^ binary_input[3])) &&
                                   (shifted_gray_code_output[0] == (binary_input[3] ^ binary_input[2]))
    );

    // Shift amount 3 preserves the Gray-code bit mapping.
    check_shift3_gray_mapping: assert property (
        @($global_clock)
        (shift_amount == 2'b11) |-> (shifted_gray_code_output[2] == (binary_input[0] ^ binary_input[3])) &&
                                   (shifted_gray_code_output[1] == (binary_input[3] ^ binary_input[2])) &&
                                   (shifted_gray_code_output[0] == (binary_input[2] ^ binary_input[1]))
    );

endmodule