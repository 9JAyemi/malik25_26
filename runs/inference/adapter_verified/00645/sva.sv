module LedOutput_sva (
    input logic clk,
    input logic [8:0] key_input,
    input logic [4:0] led_output
);

// key_input 0000000001 drives led_output to 00001.
    check_map_0000000001: assert property (
        @(posedge clk) (key_input == 9'b0000000001) |-> (led_output == 5'b00001)
    );

// key_input 0000000010 drives led_output to 00010.
    check_map_0000000010: assert property (
        @(posedge clk) (key_input == 9'b0000000010) |-> (led_output == 5'b00010)
    );

// key_input 0000000100 drives led_output to 00100.
    check_map_0000000100: assert property (
        @(posedge clk) (key_input == 9'b0000000100) |-> (led_output == 5'b00100)
    );

// key_input 0000001000 drives led_output to 01000.
    check_map_0000001000: assert property (
        @(posedge clk) (key_input == 9'b0000001000) |-> (led_output == 5'b01000)
    );

// key_input 0000010000 drives led_output to 10000.
    check_map_0000010000: assert property (
        @(posedge clk) (key_input == 9'b0000010000) |-> (led_output == 5'b10000)
    );

// key_input 0000100000 drives led_output to 00000.
    check_map_0000100000: assert property (
        @(posedge clk) (key_input == 9'b0000100000) |-> (led_output == 5'b00000)
    );

// key_input 0001000000 drives led_output to 11111.
    check_map_0001000000: assert property (
        @(posedge clk) (key_input == 9'b0001000000) |-> (led_output == 5'b11111)
    );

// Any non-matching key_input drives led_output to xxxxx.
    check_default_xxxxx: assert property (
        @(posedge clk) (key_input != 9'b0000000001 &&
                        key_input != 9'b0000000010 &&
                        key_input != 9'b0000000100 &&
                        key_input != 9'b0000001000 &&
                        key_input != 9'b0000010000 &&
                        key_input != 9'b0000100000 &&
                        key_input != 9'b0001000000) |-> (led_output == 5'bxxxxx)
    );

// led_output 00001 only occurs for key_input 0000000001.
    check_output_00001_only_for_input_0000000001: assert property (
        @(posedge clk) (led_output == 5'b00001) |-> (key_input == 9'b0000000001)
    );

// led_output 00010 only occurs for key_input 0000000010.
    check_output_00010_only_for_input_0000000010: assert property (
        @(posedge clk) (led_output == 5'b00010) |-> (key_input == 9'b0000000010)
    );

// led_output 00100 only occurs for key_input 0000000100.
    check_output_00100_only_for_input_0000000100: assert property (
        @(posedge clk) (led_output == 5'b00100) |-> (key_input == 9'b0000000100)
    );

// led_output 01000 only occurs for key_input 0000001000.
    check_output_01000_only_for_input_0000001000: assert property (
        @(posedge clk) (led_output == 5'b01000) |-> (key_input == 9'b0000001000)
    );

// led_output 10000 only occurs for key_input 0000010000.
    check_output_10000_only_for_input_0000010000: assert property (
        @(posedge clk) (led_output == 5'b10000) |-> (key_input == 9'b0000010000)
    );

// led_output 00000 only occurs for key_input 0000100000.
    check_output_00000_only_for_input_0000100000: assert property (
        @(posedge clk) (led_output == 5'b00000) |-> (key_input == 9'b0000100000)
    );

// led_output 11111 only occurs for key_input 0001000000.
    check_output_11111_only_for_input_0001000000: assert property (
        @(posedge clk) (led_output == 5'b11111) |-> (key_input == 9'b0001000000)
    );

endmodule
