module top_module_sva (
    input logic clk,
    input logic [3:0] binary_input,
    input logic [1:0] shift_amount,
    input logic [3:0] shifted_gray_code_output
);

// No RTL reset; assertions are always active.

    // Shift amount 0 passes the Gray-code input through unchanged.
    check_shift0_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (shifted_gray_code_output == gray_code_from_binary(binary_input))
    );

// Shift amount 1 rotates the Gray-code input left by one bit.
    check_shift1_rotate_left: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (shifted_gray_code_output == {gray_code_from_binary(binary_input[2:0]), gray_code_from_binary(binary_input[3])})
    );

// Shift amount 2 rotates the Gray-code input right by one bit.
    check_shift2_rotate_right: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (shifted_gray_code_output == {gray_code_from_binary(binary_input[1:0]), gray_code_from_binary(binary_input[3:2])})
    );

// Shift amount 3 rotates the Gray-code input left by two bits.
    check_shift3_rotate_left2: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (shifted_gray_code_output == {gray_code_from_binary(binary_input[0]), gray_code_from_binary(binary_input[3:1])})
    );

// The output always matches the selected shift of the Gray-code input.
    check_functional_equivalence: assert property (
        @(posedge clk)
        shifted_gray_code_output == ((shift_amount == 2'b00) ? gray_code_from_binary(binary_input) :
                                      (shift_amount == 2'b01) ? {gray_code_from_binary(binary_input[2:0]), gray_code_from_binary(binary_input[3])} :
                                      (shift_amount == 2'b10) ? {gray_code_from_binary(binary_input[1:0]), gray_code_from_binary(binary_input[3:2])} :
                                      {gray_code_from_binary(binary_input[0]), gray_code_from_binary(binary_input[3:1])})
    );

endmodule
