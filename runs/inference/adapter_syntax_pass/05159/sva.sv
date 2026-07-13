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
        sel_o == (
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00)) ? 4'b1000 :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b01)) ? 4'b0100 :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b10)) ? 4'b0010 :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b11)) ? 4'b0001 :
            ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0)) ? 4'b1100 :
            ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1)) ? 4'b0011 :
            4'b1111
        )
    );

    // mem_o matches the RTL mux expression.
    check_mem_o_mapping: assert property (
        @(posedge clk)
        mem_o == (
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00)) ? {color_i[7:0], 24'h000000} :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b01)) ? {color_i[7:0], 16'h0000}   :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b10)) ? {color_i[7:0], 8'h00}      :
            ((color_depth_i == 2'b00) && (x_lsb_i == 2'b11)) ? {color_i[7:0]}             :
            ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0)) ? {color_i[15:0], 16'h0000} :
            ((color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1)) ? {color_i[15:0]}         :
            color_i
        )
    );

    // sel_o is always one-hot or all-ones.
    check_sel_o_onehot_or_allones: assert property (
        @(posedge clk)
        $onehot(sel_o) || (sel_o == 4'b1111)
    );

    // color_depth_i=00 selects bit 7 into mem_o[7:0].
    check_depth00_selects_bit7: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) |-> (mem_o[7] == color_i[7])
    );

    // color_depth_i=01 selects bit 15 into mem_o[7:0].
    check_depth01_selects_bit15: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01) |-> (mem_o[7] == color_i[15])
    );

    // color_depth_i=10 passes the full input through.
    check_depth10_passthrough: assert property (
        @(posedge clk)
        (color_depth_i == 2'b10) |-> (mem_o == color_i)
    );

    // color_depth_i=11 passes the full input through.
    check_depth11_passthrough: assert property (
        @(posedge clk)
        (color_depth_i == 2'b11) |-> (mem_o == color_i)
    );

    // x_lsb_i=00 selects mem_o[31:24] into color_o[7:0].
    check_lsb00_selects_upper_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b00) |-> (color_o[7:0] == mem_o[31:24])
    );

    // x_lsb_i=01 selects mem_o[23:16] into color_o[7:0].
    check_lsb01_selects_middle_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b01) |-> (color_o[7:0] == mem_o[23:16])
    );

    // x_lsb_i=10 selects mem_o[15:8] into color_o[7:0].
    check_lsb10_selects_lower_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b10) |-> (color_o[7:0] == mem_o[15:8])
    );

    // x_lsb_i=11 selects mem_o[7:0] into color_o[7:0].
    check_lsb11_selects_low_nibble: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b11) |-> (color_o[7:0] == mem_o[7:0])
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
        sel_o == (
            (color_depth_i == 2'b00) ? 4'b0001 :
            (color_depth_i == 2'b01) ? 4'b0011 :
            4'b1111
        )
    );

    // sel_o is always one-hot or all-ones.
    check_sel_o_onehot_or_allones: assert property (
        @(posedge clk)
        $onehot(sel_o) || (sel_o == 4'b1111)
    );

    // color_depth_i=00 selects mem_i[31:24] into color_o[7:0].
    check_depth00_selects_upper_byte: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) |-> (color_o[7:0] == mem_i[31:24])
    );

    // color_depth_i=01 selects mem_i[15:0] into color_o[7:0].
    check_depth01_selects_low_halfword: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01) |-> (color_o[7:0] == mem_i[15:0])
    );

    // color_depth_i=10 passes the full input through.
    check_depth10_passthrough: assert property (
        @(posedge clk)
        (color_depth_i == 2'b10) |-> (color_o == mem_i)
    );

    // color_depth_i=11 passes the full input through.
    check_depth11_passthrough: assert property (
        @(posedge clk)
        (color_depth_i == 2'b11) |-> (color_o == mem_i)
    );

    // mem_lsb_i=00 selects mem_i[31:24] into color_o[7:0].
    check_lsb00_selects_upper_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b00) |-> (color_o[7:0] == mem_i[31:24])
    );

    // mem_lsb_i=01 selects mem_i[23:16] into color_o[7:0].
    check_lsb01_selects_middle_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b01) |-> (color_o[7:0] == mem_i[23:16])
    );

    // mem_lsb_i=10 selects mem_i[15:8] into color_o[7:0].
    check_lsb10_selects_lower_byte: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b10) |-> (color_o[7:0] == mem_i[15:8])
    );

    // mem_lsb_i=11 selects mem_i[7:0] into color_o[7:0].
    check_lsb11_selects_low_nibble: assert property (
        @(posedge clk)
        (mem_lsb_i == 2'b11) |-> (color_o[7:0] == mem_i[7:0])
