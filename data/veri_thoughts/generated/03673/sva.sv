module binary_to_gray_sva (
    input logic       clk,
    input logic [2:0] B,
    input logic [2:0] G
);

    // 000 maps to 000.
    check_b000_maps_to_g000: assert property (
        @(posedge clk) (B == 3'b000) |-> (G == 3'b000)
    );

    // 001 maps to 001.
    check_b001_maps_to_g001: assert property (
        @(posedge clk) (B == 3'b001) |-> (G == 3'b001)
    );

    // 010 maps to 011.
    check_b010_maps_to_g011: assert property (
        @(posedge clk) (B == 3'b010) |-> (G == 3'b011)
    );

    // 011 maps to 010.
    check_b011_maps_to_g010: assert property (
        @(posedge clk) (B == 3'b011) |-> (G == 3'b010)
    );

    // 100 maps to 110.
    check_b100_maps_to_g110: assert property (
        @(posedge clk) (B == 3'b100) |-> (G == 3'b110)
    );

    // 101 maps to 111.
    check_b101_maps_to_g111: assert property (
        @(posedge clk) (B == 3'b101) |-> (G == 3'b111)
    );

    // 110 maps to 101.
    check_b110_maps_to_g101: assert property (
        @(posedge clk) (B == 3'b110) |-> (G == 3'b101)
    );

    // 111 maps to 100.
    check_b111_maps_to_g100: assert property (
        @(posedge clk) (B == 3'b111) |-> (G == 3'b100)
    );

endmodule