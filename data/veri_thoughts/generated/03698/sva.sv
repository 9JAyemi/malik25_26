module top_module_assertions (
    input logic clk,
    input logic [3:0] binary_input,
    input logic [1:0] shift_amount,
    input logic [3:0] shifted_gray_code_output
);

    // No shift selects the direct Gray-code encoding.
    check_no_shift_gray_mapping: assert property (
        @(posedge clk)
        (shift_amount == 2'b00) |-> (
            shifted_gray_code_output ==
            {binary_input[3],
             (binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0])}
        )
    );

    // Shift amount 1 rotates the Gray code left by 1 bit.
    check_shift_by_1_gray_rotation: assert property (
        @(posedge clk)
        (shift_amount == 2'b01) |-> (
            shifted_gray_code_output ==
            {(binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0]),
             binary_input[3]}
        )
    );

    // Shift amount 2 rotates the Gray code left by 2 bits.
    check_shift_by_2_gray_rotation: assert property (
        @(posedge clk)
        (shift_amount == 2'b10) |-> (
            shifted_gray_code_output ==
            {(binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0]),
             binary_input[3],
             (binary_input[3] ^ binary_input[2])}
        )
    );

    // Shift amount 3 rotates the Gray code left by 3 bits.
    check_shift_by_3_gray_rotation: assert property (
        @(posedge clk)
        (shift_amount == 2'b11) |-> (
            shifted_gray_code_output ==
            {(binary_input[1] ^ binary_input[0]),
             binary_input[3],
             (binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1])}
        )
    );

    // The top-level output always matches the composed Gray encoder and shifter.
    check_end_to_end_function: assert property (
        @(posedge clk)
        shifted_gray_code_output ==
        ((shift_amount == 2'b00) ?
            {binary_input[3],
             (binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0])} :
         (shift_amount == 2'b01) ?
            {(binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0]),
             binary_input[3]} :
         (shift_amount == 2'b10) ?
            {(binary_input[2] ^ binary_input[1]),
             (binary_input[1] ^ binary_input[0]),
             binary_input[3],
             (binary_input[3] ^ binary_input[2])} :
            {(binary_input[1] ^ binary_input[0]),
             binary_input[3],
             (binary_input[3] ^ binary_input[2]),
             (binary_input[2] ^ binary_input[1])})
    );

endmodule