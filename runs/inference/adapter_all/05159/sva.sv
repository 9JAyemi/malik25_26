module color_to_memory_sva (
    input logic        clk,
    input logic [1:0]  color_depth_i,
    input logic [31:0] color_i,
    input logic [1:0]  x_lsb_i,
    input logic [31:0] mem_o,
    input logic [3:0]  sel_o
);

    // sel_o matches the RTL mux expression.
    check_sel_o_mapping: assert property (
        @(posedge clk)
        sel_o == ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00) ? 4'b1000 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b01) ? 4'b0100 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b10) ? 4'b0010 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b11) ? 4'b0001 :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0)  ? 4'b1100  :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1)  ? 4'b0011  : 4'b1111)
    );

    // mem_o matches the RTL mux expression.
    check_mem_o_mapping: assert property (
        @(posedge clk)
        mem_o == ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00) ? {color_i[7:0], 24'h000000} :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b01) ? {color_i[7:0], 16'h0000}   :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b10) ? {color_i[7:0], 8'h00}      :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b11) ? {color_i[7:0]}             :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0)  ? {color_i[15:0], 16'h0000}   :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1)  ? {color_i[15:0]}             : color_i)
    );

    // color_depth_i 00 with x_lsb_i 00 selects mem_o[31:24].
    check_sel_0000: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b00) |-> (sel_o == 4'b1000)
    );

    // color_depth_i 00 with x_lsb_i 01 selects mem_o[23:16].
    check_sel_0001: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b01) |-> (sel_o == 4'b0100)
    );

    // color_depth_i 00 with x_lsb_i 10 selects mem_o[15:8].
    check_sel_0010: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b10) |-> (sel_o == 4'b0010)
    );

    // color_depth_i 00 with x_lsb_i 11 selects mem_o[7:0].
    check_sel_0011: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b11) |-> (sel_o == 4'b0001)
    );

    // color_depth_i 01 with x_lsb_i 00 selects mem_o[31:16].
    check_sel_0100: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i == 2'b00) |-> (sel_o == 4'b1100)
    );

    // color_depth_i 01 with x_lsb_i 01 selects mem_o[15:0].
    check_sel_0101: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i == 2'b01) |-> (sel_o == 4'b0011)
    );

    // color_depth_i 01 with x_lsb_i 10 or 11 selects all bits.
    check_sel_0111: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i[0] == 1'b1) |-> (sel_o == 4'b1111)
    );

    // color_depth_i 10 or 11 selects all bits.
    check_sel_1111: assert property (
        @(posedge clk)
        (color_depth_i[1] == 1'b1) |-> (sel_o == 4'b1111)
    );

    // color_depth_i 00 with x_lsb_i 00 maps to upper byte and zeroed lower bits.
    check_mem_0000: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b00) |-> (mem_o == {color_i[7:0], 24'h000000})
    );

    // color_depth_i 00 with x_lsb_i 01 maps to upper byte and zeroed lower bits.
    check_mem_0001: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b01) |-> (mem_o == {color_i[7:0], 16'h0000})
    );

    // color_depth_i 00 with x_lsb_i 10 maps to upper byte and zeroed lower bits.
    check_mem_0010: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b10) |-> (mem_o == {color_i[7:0], 8'h00})
    );

    // color_depth_i 00 with x_lsb_i 11 maps to upper byte only.
    check_mem_0011: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00 && x_lsb_i == 2'b11) |-> (mem_o == {color_i[7:0]})
    );

    // color_depth_i 01 with x_lsb_i 00 maps to upper halfword and zeroed lower bits.
    check_mem_0100: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i == 2'b00) |-> (mem_o == {color_i[15:0], 16'h0000})
    );

    // color_depth_i 01 with x_lsb_i 01 maps to upper halfword only.
    check_mem_0101: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i == 2'b01) |-> (mem_o == {color_i[15:0]})
    );

    // color_depth_i 01 with x_lsb_i 10 or 11 maps to all bits.
    check_mem_0111: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01 && x_lsb_i[0] == 1'b1) |-> (mem_o == color_i)
    );

    // color_depth_i 10 or 11 maps to all bits.
    check_mem_1111: assert property (
        @(posedge clk)
        (color_depth_i[1] == 1'b1) |-> (mem_o == color_i)
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

    // sel_o matches the RTL mux expression.
    check_sel_o_mapping: assert property (
        @(posedge clk)
        sel_o == (color_depth_i == 2'b00 ? 