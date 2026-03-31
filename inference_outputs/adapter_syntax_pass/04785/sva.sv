module decimal_to_binary_sva (
    input logic clk,
    input logic [3:0] in_value,
    input logic [3:0] out_value
);

    // 0 maps to 0000.
    check_map_0: assert property (
        @(posedge clk) (in_value == 4'd0) |-> (out_value == 4'b0000)
    );

    // 1 maps to 0001.
    check_map_1: assert property (
        @(posedge clk) (in_value == 4'd1) |-> (out_value == 4'b0001)
    );

    // 2 maps to 0010.
    check_map_2: assert property (
        @(posedge clk) (in_value == 4'd2) |-> (out_value == 4'b0010)
    );

    // 3 maps to 0011.
    check_map_3: assert property (
        @(posedge clk) (in_value == 4'd3) |-> (out_value == 4'b0011)
    );

    // 4 maps to 0100.
    check_map_4: assert property (
        @(posedge clk) (in_value == 4'd4) |-> (out_value == 4'b0100)
    );

    // 5 maps to 0101.
    check_map_5: assert property (
        @(posedge clk) (in_value == 4'd5) |-> (out_value == 4'b0101)
    );

    // 6 maps to 0110.
    check_map_6: assert property (
        @(posedge clk) (in_value == 4'd6) |-> (out_value == 4'b0110)
    );

    // 7 maps to 0111.
    check_map_7: assert property (
        @(posedge clk) (in_value == 4'd7) |-> (out_value == 4'b0111)
    );

    // 8 maps to 1000.
    check_map_8: assert property (
        @(posedge clk) (in_value == 4'd8) |-> (out_value == 4'b1000)
    );

    // 9 maps to 1001.
    check_map_9: assert property (
        @(posedge clk) (in_value == 4'd9) |-> (out_value == 4'b1001)
    );

    // Values 10 through 15 drive X.
    check_default_x: assert property (
        @(posedge clk) (in_value >= 4'd10) |-> (out_value == 4'bXXXX)
    );

endmodule