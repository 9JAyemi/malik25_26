module top_module_sva (
    input logic [3:0] binary_input,
    input logic [1:0] shift_amount,
    input logic [3:0] shifted_gray_code_output
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Shift 00 passes the Gray code through unchanged.
    check_shift00_passthrough: assert property (
        @($global_clock)
        (shift_amount == 2'b00) |-> (shifted_gray_code_output == {binary_input[3], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Shift 01 rotates the Gray code left by one bit.
    check_shift01_rotate_left1: assert property (
        @($global_clock)
        (shift_amount == 2'b01) |-> (shifted_gray_code_output == {binary_input[2], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Shift 10 rotates the Gray code left by two bits.
    check_shift10_rotate_left2: assert property (
        @($global_clock)
        (shift_amount == 2'b10) |-> (shifted_gray_code_output == {binary_input[1], binary_input[0], binary_input[3], binary_input[2]})
    );

    // Shift 11 rotates the Gray code left by three bits.
    check_shift11_rotate_left3: assert property (
        @($global_clock)
        (shift_amount == 2'b11) |-> (shifted_gray_code_output == {binary_input[0], binary_input[3], binary_input[2], binary_input[1]})
    );

    // Left rotation by one bit is equivalent to the Gray code of the rotated binary input.
    check_gray_of_rotated_binary: assert property (
        @($global_clock)
        (shift_amount == 2'b01) |-> (shifted_gray_code_output == {binary_input[2], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Left rotation by two bits is equivalent to the Gray code of the rotated binary input.
    check_gray_of_rotated_binary2: assert property (
        @($global_clock)
        (shift_amount == 2'b10) |-> (shifted_gray_code_output == {binary_input[1], binary_input[0], binary_input[3], binary_input[2]})
    );

    // Left rotation by three bits is equivalent to the Gray code of the rotated binary input.
    check_gray_of_rotated_binary3: assert property (
        @($global_clock)
        (shift_amount == 2'b11) |-> (shifted_gray_code_output == {binary_input[0], binary_input[3], binary_input[2], binary_input[1]})
    );

endmodule