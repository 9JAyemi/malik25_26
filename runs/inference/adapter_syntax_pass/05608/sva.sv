module binary_converter_sva (
    input logic clk,
    input logic [9:0] input_val,
    input logic [3:0] binary_val
);

    // 0 maps to 0000.
    check_map_0000000000: assert property (
        @(posedge clk) (input_val == 10'b0000000000) |-> (binary_val == 4'b0000)
    );

    // 1 maps to 0001.
    check_map_0000000001: assert property (
        @(posedge clk) (input_val == 10'b0000000001) |-> (binary_val == 4'b0001)
    );

    // 2 maps to 0010.
    check_map_0000000010: assert property (
        @(posedge clk) (input_val == 10'b0000000010) |-> (binary_val == 4'b0010)
    );

    // 3 maps to 0011.
    check_map_0000000011: assert property (
        @(posedge clk) (input_val == 10'b0000000011) |-> (binary_val == 4'b0011)
    );

    // 4 maps to 0100.
    check_map_0000000100: assert property (
        @(posedge clk) (input_val == 10'b0000000100) |-> (binary_val == 4'b0100)
    );

    // 5 maps to 0101.
    check_map_0000000101: assert property (
        @(posedge clk) (input_val == 10'b0000000101) |-> (binary_val == 4'b0101)
    );

    // 6 maps to 0110.
    check_map_0000000110: assert property (
        @(posedge clk) (input_val == 10'b0000000110) |-> (binary_val == 4'b0110)
    );

    // 7 maps to 0111.
    check_map_0000000111: assert property (
        @(posedge clk) (input_val == 10'b0000000111) |-> (binary_val == 4'b0111)
    );

    // 8 maps to 1000.
    check_map_0000001000: assert property (
        @(posedge clk) (input_val == 10'b0000001000) |-> (binary_val == 4'b1000)
    );

    // 9 maps to 1001.
    check_map_0000001001: assert property (
        @(posedge clk) (input_val == 10'b0000001001) |-> (binary_val == 4'b1001)
    );

    // Values above 9 map to 0000.
    check_map_default: assert property (
        @(posedge clk) (input_val >= 10'b0000001010) |-> (binary_val == 4'b0000)
    );

endmodule