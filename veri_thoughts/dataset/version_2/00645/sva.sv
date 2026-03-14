module LedOutput_sva (
    input logic clk,                 // sampling clock for assertions
    input logic [8:0] key_input,
    input logic [4:0] led_output
);
    // key_input == 1 maps to led_output == 00001
    map_1_to_00001: assert property (
        @(posedge clk) (key_input == 9'h001) |-> (led_output == 5'b00001)
    );
    // key_input == 2 maps to led_output == 00010
    map_2_to_00010: assert property (
        @(posedge clk) (key_input == 9'h002) |-> (led_output == 5'b00010)
    );
    // key_input == 4 maps to led_output == 00100
    map_4_to_00100: assert property (
        @(posedge clk) (key_input == 9'h004) |-> (led_output == 5'b00100)
    );
    // key_input == 8 maps to led_output == 01000
    map_8_to_01000: assert property (
        @(posedge clk) (key_input == 9'h008) |-> (led_output == 5'b01000)
    );
    // key_input == 16 maps to led_output == 10000
    map_16_to_10000: assert property (
        @(posedge clk) (key_input == 9'h010) |-> (led_output == 5'b10000)
    );
    // key_input == 32 maps to led_output == 00000
    map_32_to_00000: assert property (
        @(posedge clk) (key_input == 9'h020) |-> (led_output == 5'b00000)
    );
    // key_input == 64 maps to led_output == 11111
    map_64_to_11111: assert property (
        @(posedge clk) (key_input == 9'h040) |-> (led_output == 5'b11111)
    );

    // For defined keys, led_output has no unknown bits
    no_x_led_when_defined: assert property (
        @(posedge clk)
        ((key_input == 9'h001) || (key_input == 9'h002) || (key_input == 9'h004) ||
         (key_input == 9'h008) || (key_input == 9'h010) || (key_input == 9'h020) ||
         (key_input == 9'h040)) |-> !$isunknown(led_output)
    );

    // led_output == 00001 only occurs when key_input == 1
    inv_00001_only_with_1: assert property (
        @(posedge clk) (led_output == 5'b00001) |-> (key_input == 9'h001)
    );
    // led_output == 00010 only occurs when key_input == 2
    inv_00010_only_with_2: assert property (
        @(posedge clk) (led_output == 5'b00010) |-> (key_input == 9'h002)
    );
    // led_output == 00100 only occurs when key_input == 4
    inv_00100_only_with_4: assert property (
        @(posedge clk) (led_output == 5'b00100) |-> (key_input == 9'h004)
    );
    // led_output == 01000 only occurs when key_input == 8
    inv_01000_only_with_8: assert property (
        @(posedge clk) (led_output == 5'b01000) |-> (key_input == 9'h008)
    );
    // led_output == 10000 only occurs when key_input == 16
    inv_10000_only_with_16: assert property (
        @(posedge clk) (led_output == 5'b10000) |-> (key_input == 9'h010)
    );
    // led_output == 00000 only occurs when key_input == 32
    inv_00000_only_with_32: assert property (
        @(posedge clk) (led_output == 5'b00000) |-> (key_input == 9'h020)
    );
    // led_output == 11111 only occurs when key_input == 64
    inv_11111_only_with_64: assert property (
        @(posedge clk) (led_output == 5'b11111) |-> (key_input == 9'h040)
    );
endmodule