module LedOutput_sva (
    input logic [8:0] key_input,
    input logic [4:0] led_output
);

    // 0000000001 maps to 00001.
    check_map_0000000001: assert property (
        @($global_clock) (key_input == 9'b0000000001) |-> (led_output == 5'b00001)
    );

    // 0000000010 maps to 00010.
    check_map_0000000010: assert property (
        @($global_clock) (key_input == 9'b0000000010) |-> (led_output == 5'b00010)
    );

    // 0000000100 maps to 00100.
    check_map_0000000100: assert property (
        @($global_clock) (key_input == 9'b0000000100) |-> (led_output == 5'b00100)
    );

    // 0000001000 maps to 01000.
    check_map_0000001000: assert property (
        @($global_clock) (key_input == 9'b0000001000) |-> (led_output == 5'b01000)
    );

    // 0000010000 maps to 10000.
    check_map_0000010000: assert property (
        @($global_clock) (key_input == 9'b0000010000) |-> (led_output == 5'b10000)
    );

    // 0000100000 maps to 00000.
    check_map_0000100000: assert property (
        @($global_clock) (key_input == 9'b0000100000) |-> (led_output == 5'b00000)
    );

    // 0001000000 maps to 11111.
    check_map_0001000000: assert property (
        @($global_clock) (key_input == 9'b0001000000) |-> (led_output == 5'b11111)
    );

    // Any non-listed key_input drives the default unknown value.
    check_default_unknown: assert property (
        @($global_clock)
        ((key_input != 9'b0000000001) &&
         (key_input != 9'b0000000010) &&
         (key_input != 9'b0000000100) &&
         (key_input != 9'b0000001000) &&
         (key_input != 9'b0000010000) &&
         (key_input != 9'b0000100000) &&
         (key_input != 9'b0001000000))
        |-> (led_output == 5'bxxxxx)
    );

endmodule