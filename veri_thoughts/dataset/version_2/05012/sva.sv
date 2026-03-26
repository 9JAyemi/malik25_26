module top_module_assertions (
    input logic       CLK,
    input logic       RESET,
    input logic [2:0] in,
    input logic       enable,
    input logic       SHIFT_LEFT,
    input logic       SHIFT_RIGHT,
    input logic [3:0] DATA,
    input logic [7:0] out
);

    // Full output matches the decoder result ORed with the shifter result.
    check_out_function: assert property (
        @(posedge CLK) disable iff (RESET)
        out == (((enable) ? (8'b00000001 << in) : 8'b00000000) |
                ((SHIFT_LEFT) ? {4'b0000, DATA[2:0], 1'b0} :
                 (SHIFT_RIGHT) ? {4'b0000, 1'b0, DATA[3:1]} :
                                 {4'b0000, DATA}))
    );

    // Upper nibble is zero unless the decoder selects bits 4 through 7.
    check_upper_nibble_zero_without_high_decode: assert property (
        @(posedge CLK) disable iff (RESET)
        (!enable || (in < 3'd4)) |-> (out[7:4] == 4'b0000)
    );

    // High decoder selections appear exactly in the upper nibble.
    check_upper_nibble_high_decode: assert property (
        @(posedge CLK) disable iff (RESET)
        (enable && (in >= 3'd4)) |-> (out[7:4] == (4'b0001 << (in - 3'd4)))
    );

    // When enabled, the selected decoder output bit must be asserted.
    check_decoder_selected_bit_set: assert property (
        @(posedge CLK) disable iff (RESET)
        enable |-> (out[in] == 1'b1)
    );

    // Left shift mode determines the shifter contribution to the low nibble.
    check_shift_left_low_nibble: assert property (
        @(posedge CLK) disable iff (RESET)
        SHIFT_LEFT |-> (out[3:0] == ({DATA[2:0], 1'b0} | ((enable) ? (4'b0001 << in) : 4'b0000)))
    );

    // Right shift mode applies when left shift is not asserted.
    check_shift_right_low_nibble: assert property (
        @(posedge CLK) disable iff (RESET)
        (!SHIFT_LEFT && SHIFT_RIGHT) |-> (out[3:0] == ({1'b0, DATA[3:1]} | ((enable) ? (4'b0001 << in) : 4'b0000)))
    );

    // With no shift control asserted, DATA passes through the shifter.
    check_no_shift_low_nibble: assert property (
        @(posedge CLK) disable iff (RESET)
        (!SHIFT_LEFT && !SHIFT_RIGHT) |-> (out[3:0] == (DATA | ((enable) ? (4'b0001 << in) : 4'b0000)))
    );

    // Left shift has priority when both shift controls are asserted.
    check_shift_left_priority: assert property (
        @(posedge CLK) disable iff (RESET)
        (SHIFT_LEFT && SHIFT_RIGHT) |-> (out[3:0] == ({DATA[2:0], 1'b0} | ((enable) ? (4'b0001 << in) : 4'b0000)))
    );

endmodule