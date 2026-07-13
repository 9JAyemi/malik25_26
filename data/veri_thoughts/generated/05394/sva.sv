module excess_3_converter_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [7:0] excess_3
);

    // Binary 0 maps to the expected encoded value.
    check_binary_0_encoding: assert property (
        @(posedge clk) (binary == 4'd0) |-> (excess_3 == 8'b0011_0011)
    );

    // Binary 1 maps to the expected encoded value.
    check_binary_1_encoding: assert property (
        @(posedge clk) (binary == 4'd1) |-> (excess_3 == 8'b0011_0100)
    );

    // Binary 2 maps to the expected encoded value.
    check_binary_2_encoding: assert property (
        @(posedge clk) (binary == 4'd2) |-> (excess_3 == 8'b0011_0101)
    );

    // Binary 3 maps to the expected encoded value.
    check_binary_3_encoding: assert property (
        @(posedge clk) (binary == 4'd3) |-> (excess_3 == 8'b0011_0110)
    );

    // Binary 4 maps to the expected encoded value.
    check_binary_4_encoding: assert property (
        @(posedge clk) (binary == 4'd4) |-> (excess_3 == 8'b0011_0111)
    );

    // Binary 5 maps to the expected encoded value.
    check_binary_5_encoding: assert property (
        @(posedge clk) (binary == 4'd5) |-> (excess_3 == 8'b0011_1000)
    );

    // Binary 6 maps to the expected encoded value.
    check_binary_6_encoding: assert property (
        @(posedge clk) (binary == 4'd6) |-> (excess_3 == 8'b0011_1001)
    );

    // Binary 7 maps to the expected encoded value.
    check_binary_7_encoding: assert property (
        @(posedge clk) (binary == 4'd7) |-> (excess_3 == 8'b0011_1010)
    );

    // Binary 8 maps to the expected encoded value.
    check_binary_8_encoding: assert property (
        @(posedge clk) (binary == 4'd8) |-> (excess_3 == 8'b0011_1011)
    );

    // Binary 9 maps to the expected encoded value.
    check_binary_9_encoding: assert property (
        @(posedge clk) (binary == 4'd9) |-> (excess_3 == 8'b0011_1100)
    );

    // Binary 10 maps to the expected encoded value.
    check_binary_10_encoding: assert property (
        @(posedge clk) (binary == 4'd10) |-> (excess_3 == 8'b0011_1101)
    );

    // Binary 11 maps to the expected encoded value.
    check_binary_11_encoding: assert property (
        @(posedge clk) (binary == 4'd11) |-> (excess_3 == 8'b0011_1110)
    );

    // Binary 12 maps to the expected encoded value.
    check_binary_12_encoding: assert property (
        @(posedge clk) (binary == 4'd12) |-> (excess_3 == 8'b0011_1111)
    );

    // Binary 13 maps to the expected encoded value.
    check_binary_13_encoding: assert property (
        @(posedge clk) (binary == 4'd13) |-> (excess_3 == 8'b0100_0000)
    );

    // Binary 14 maps to the expected encoded value.
    check_binary_14_encoding: assert property (
        @(posedge clk) (binary == 4'd14) |-> (excess_3 == 8'b0100_0001)
    );

    // Binary 15 maps to the expected encoded value.
    check_binary_15_encoding: assert property (
        @(posedge clk) (binary == 4'd15) |-> (excess_3 == 8'b0100_0010)
    );

endmodule