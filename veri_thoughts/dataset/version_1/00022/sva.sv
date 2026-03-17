module keypad_left_shift_sva (
    input logic       clk,
    input logic [3:0] col,
    input logic [7:0] out,
    input logic [3:0] row,
    input logic [3:0] key_pressed,
    input logic [3:0] shifted_key_pressed
);

    // Row is forced to the fixed scan value each cycle.
    check_row_constant: assert property (
        @(posedge clk) 1'b1 |=> (row === 4'b1110)
    );

    // Column 1110 decodes to key 0001.
    check_key_decode_col_1110: assert property (
        @(posedge clk) (col === 4'b1110) |=> (key_pressed === 4'b0001)
    );

    // Column 1101 decodes to key 0010.
    check_key_decode_col_1101: assert property (
        @(posedge clk) (col === 4'b1101) |=> (key_pressed === 4'b0010)
    );

    // Column 1011 decodes to key 0100.
    check_key_decode_col_1011: assert property (
        @(posedge clk) (col === 4'b1011) |=> (key_pressed === 4'b0100)
    );

    // Column 0111 decodes to key 1000.
    check_key_decode_col_0111: assert property (
        @(posedge clk) (col === 4'b0111) |=> (key_pressed === 4'b1000)
    );

    // Any other column pattern decodes to 0000.
    check_key_decode_default: assert property (
        @(posedge clk)
        ((col !== 4'b1110) && (col !== 4'b1101) && (col !== 4'b1011) && (col !== 4'b0111))
        |=> (key_pressed === 4'b0000)
    );

    // Decoded key is always one-hot or zero.
    check_key_pressed_legal_values: assert property (
        @(posedge clk) 1'b1 |=> (
            (key_pressed === 4'b0000) ||
            (key_pressed === 4'b0001) ||
            (key_pressed === 4'b0010) ||
            (key_pressed === 4'b0100) ||
            (key_pressed === 4'b1000)
        )
    );

    // Shifted key is the previous key rotated left by one bit.
    check_shifted_key_rotation: assert property (
        @(posedge clk) 1'b1 |=> (
            shifted_key_pressed === { $past(key_pressed[2:0]), $past(key_pressed[3]) }
        )
    );

    // Output low nibble captures the previous key code.
    check_out_lower_captures_previous_key: assert property (
        @(posedge clk) 1'b1 |=> (out[3:0] === $past(key_pressed))
    );

    // Output high nibble captures the previous shifted key code.
    check_out_upper_captures_previous_shift: assert property (
        @(posedge clk) 1'b1 |=> (out[7:4] === $past(shifted_key_pressed))
    );

endmodule