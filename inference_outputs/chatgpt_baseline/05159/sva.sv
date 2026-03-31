module color_to_memory_sva (
    input logic        clk,
    input logic [1:0]  color_depth_i,
    input logic [31:0] color_i,
    input logic [1:0]  x_lsb_i,
    input logic [31:0] mem_o,
    input logic [3:0]  sel_o
);

    // 8-bit color at byte lane 3 maps to sel 1000 and upper byte data.
    check_depth8_x00_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00)) |->
        ((sel_o == 4'b1000) && (mem_o == {color_i[7:0], 24'h000000}))
    );

    // 8-bit color at byte lane 2 maps to sel 0100 and bits [23:16].
    check_depth8_x01_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (x_lsb_i == 2'b01)) |->
        ((sel_o == 4'b0100) && (mem_o == {8'h00, color_i[7:0], 16'h0000}))
    );

    // 8-bit color at byte lane 1 maps to sel 0010 and bits [15:8].
    check_depth8_x10_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (x_lsb_i == 2'b10)) |->
        ((sel_o == 4'b0010) && (mem_o == {16'h0000, color_i[7:0], 8'h00}))
    );

    // 8-bit color at byte lane 0 maps to sel 0001 and bits [7:0].
    check_depth8_x11_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (x_lsb_i == 2'b11)) |->
        ((sel_o == 4'b0001) && (mem_o == {24'h000000, color_i[7:0]}))
    );

    // 16-bit color on even halfword maps to sel 1100 and upper halfword data.
    check_depth16_even_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0)) |->
        ((sel_o == 4'b1100) && (mem_o == {color_i[15:0], 16'h0000}))
    );

    // 16-bit color on odd halfword maps to sel 0011 and lower halfword data.
    check_depth16_odd_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1)) |->
        ((sel_o == 4'b0011) && (mem_o == {16'h0000, color_i[15:0]}))
    );

    // Other color depths pass through full word data and select all bytes.
    check_other_depth_passthrough: assert property (
        @(posedge clk)
        ((color_depth_i != 2'b00) && (color_depth_i != 2'b01)) |->
        ((sel_o == 4'b1111) && (mem_o == color_i))
    );

endmodule

module memory_to_color_sva (
    input logic        clk,
    input logic [1:0]  color_depth_i,
    input logic [31:0] mem_i,
    input logic [1:0]  mem_lsb_i,
    input logic [31:0] color_o,
    input logic [3:0]  sel_o
);

    // 8-bit color from byte lane 3 maps to sel 0001 and low byte output.
    check_depth8_mem00_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (mem_lsb_i == 2'b00)) |->
        ((sel_o == 4'b0001) && (color_o == {24'h000000, mem_i[31:24]}))
    );

    // 8-bit color from byte lane 2 maps to sel 0001 and low byte output.
    check_depth8_mem01_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (mem_lsb_i == 2'b01)) |->
        ((sel_o == 4'b0001) && (color_o == {24'h000000, mem_i[23:16]}))
    );

    // 8-bit color from byte lane 1 maps to sel 0001 and low byte output.
    check_depth8_mem10_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (mem_lsb_i == 2'b10)) |->
        ((sel_o == 4'b0001) && (color_o == {24'h000000, mem_i[15:8]}))
    );

    // 8-bit color from byte lane 0 maps to sel 0001 and low byte output.
    check_depth8_mem11_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b00) && (mem_lsb_i == 2'b11)) |->
        ((sel_o == 4'b0001) && (color_o == {24'h000000, mem_i[7:0]}))
    );

    // 16-bit color from upper halfword maps to sel 0011 and low halfword output.
    check_depth16_even_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b01) && (mem_lsb_i[0] == 1'b0)) |->
        ((sel_o == 4'b0011) && (color_o == {16'h0000, mem_i[31:16]}))
    );

    // 16-bit color from lower halfword maps to sel 0011 and low halfword output.
    check_depth16_odd_mapping: assert property (
        @(posedge clk)
        ((color_depth_i == 2'b01) && (mem_lsb_i[0] == 1'b1)) |->
        ((sel_o == 4'b0011) && (color_o == {16'h0000, mem_i[15:0]}))
    );

    // Other color depths pass through full word data and select all bytes.
    check_other_depth_passthrough: assert property (
        @(posedge clk)
        ((color_depth_i != 2'b00) && (color_depth_i != 2'b01)) |->
        ((sel_o == 4'b1111) && (color_o == mem_i))
    );

endmodule