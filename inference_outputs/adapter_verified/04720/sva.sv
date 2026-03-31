module functional_module_sva (
    input logic clk,
    input logic [3:0] B,
    input logic [1:0] in,
    input logic [15:0] out
);

// out must always be one-hot.
    check_out_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

// in=00 selects bit 0.
    check_decode_in00: assert property (
        @(posedge clk) (in == 2'b00) |-> (out == 16'h0001)
    );

// in=01 selects bit 1.
    check_decode_in01: assert property (
        @(posedge clk) (in == 2'b01) |-> (out == 16'h0002)
    );

// in=10 selects bit 2.
    check_decode_in10: assert property (
        @(posedge clk) (in == 2'b10) |-> (out == 16'h0004)
    );

// in=11 selects bit 3.
    check_decode_in11: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == 16'h0008)
    );

// B=0000 maps to E=0011 and out=0001.
    check_map_b0000: assert property (
        @(posedge clk) (B == 4'h0) |-> ((out == 16'h0001) && (in == 2'b00))
    );

// B=0001 maps to E=0100 and out=0010.
    check_map_b0001: assert property (
        @(posedge clk) (B == 4'h1) |-> ((out == 16'h0002) && (in == 2'b01))
    );

// B=0010 maps to E=0101 and out=0100.
    check_map_b0010: assert property (
        @(posedge clk) (B == 4'h2) |-> ((out == 16'h0004) && (in == 2'b10))
    );

// B=0011 maps to E=0110 and out=1000.
    check_map_b0011: assert property (
        @(posedge clk) (B == 4'h3) |-> ((out == 16'h0008) && (in == 2'b11))
    );

// B=0100 maps to E=0111 and out=0001.
    check_map_b0100: assert property (
        @(posedge clk) (B == 4'h4) |-> ((out == 16'h0001) && (in == 2'b00))
    );

// B=0101 maps to E=1000 and out=0010.
    check_map_b0101: assert property (
        @(posedge clk) (B == 4'h5) |-> ((out == 16'h0002) && (in == 2'b01))
    );

// B=0110 maps to E=1001 and out=0100.
    check_map_b0110: assert property (
        @(posedge clk) (B == 4'h6) |-> ((out == 16'h0004) && (in == 2'b10))
    );

// B=0111 maps to E=1010 and out=1000.
    check_map_b0111: assert property (
        @(posedge clk) (B == 4'h7) |-> ((out == 16'h0008) && (in == 2'b11))
    );

// B=1000 maps to E=1011 and out=0001.
    check_map_b1000: assert property (
        @(posedge clk) (B == 4'h8) |-> ((out == 16'h0001) && (in == 2'b00))
    );

// B=1001 maps to E=1100 and out=0010.
    check_map_b1001: assert property (
        @(posedge clk) (B == 4'h9) |-> ((out == 16'h0002) && (in == 2'b01))
    );

// B=1010 maps to E=1101 and out=0100.
    check_map_b1010: assert property (
        @(posedge clk) (B == 4'hA) |-> ((out == 16'h0004) && (in == 2'b10))
    );

// B=1011 maps to E=1110 and out=1000.
    check_map_b1011: assert property (
        @(posedge clk) (B == 4'hB) |-> ((out == 16'h0008) && (in == 2'b11))
    );

// B=1100 maps to E=1111 and out=0001.
    check_map_b1100: assert property (
        @(posedge clk) (B == 4'hC) |-> ((out == 16'h0001) && (in == 2'b00))
    );

// B=1101 maps to E=0001 and out=0010.
    check_map_b1101: assert property (
        @(posedge clk) (B == 4'hD) |-> ((out == 16'h0002) && (in == 2'b01))
    );

// B=1110 maps to E=0010 and out=0100.
    check_map_b1110: assert property (
        @(posedge clk) (B == 4'hE) |-> ((out == 16'h0004) && (in == 2'b10))
    );

// B=1111 maps to E=0011 and out=1000.
    check_map_b1111: assert property (
        @(posedge clk) (B == 4'hF) |-> ((out == 16'h0008) && (in == 2'b11))
    );

endmodule
