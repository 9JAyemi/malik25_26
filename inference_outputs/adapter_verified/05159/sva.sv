module color_to_memory_sva (
    input logic        clk,
    input logic [1:0]  color_depth_i,
    input logic [31:0] color_i,
    input logic [1:0]  x_lsb_i,
    input logic [31:0] mem_o,
    input logic [3:0]  sel_o
);

// sel_o matches the RTL mux expression.
    check_sel_o_mux: assert property (
        @(posedge clk)
        sel_o == ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00) ? 4'b1000 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b01) ? 4'b0100 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b10) ? 4'b0010 :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b11) ? 4'b0001 :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0) ? 4'b1100 :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1) ? 4'b0011 :
                  4'b1111)
    );

// mem_o matches the RTL mux expression.
    check_mem_o_mux: assert property (
        @(posedge clk)
        mem_o == ((color_depth_i == 2'b00) && (x_lsb_i == 2'b00) ? {color_i[7:0], 24'h000000} :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b01) ? {color_i[7:0], 16'h0000}   :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b10) ? {color_i[7:0], 8'h00}      :
                  (color_depth_i == 2'b00) && (x_lsb_i == 2'b11) ? {color_i[7:0]}             :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0) ? {color_i[15:0], 16'h0000}  :
                  (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1) ? {color_i[15:0]}           :
                  color_i)
    );

// For color_depth_i==00 and x_lsb_i==00, sel_o must be 1000 and mem_o must be {color_i[7:0], 24'h000000}.
    check_sel_mem_00_00: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) && (x_lsb_i == 2'b00) |-> (sel_o == 4'b1000) && (mem_o == {color_i[7:0], 24'h000000})
    );

// For color_depth_i==00 and x_lsb_i==01, sel_o must be 0100 and mem_o must be {color_i[7:0], 16'h0000}.
    check_sel_mem_00_01: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) && (x_lsb_i == 2'b01) |-> (sel_o == 4'b0100) && (mem_o == {color_i[7:0], 16'h0000})
    );

// For color_depth_i==00 and x_lsb_i==10, sel_o must be 0010 and mem_o must be {color_i[7:0], 8'h00}.
    check_sel_mem_00_10: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) && (x_lsb_i == 2'b10) |-> (sel_o == 4'b0010) && (mem_o == {color_i[7:0], 8'h00})
    );

// For color_depth_i==00 and x_lsb_i==11, sel_o must be 0001 and mem_o must be {color_i[7:0]}.
    check_sel_mem_00_11: assert property (
        @(posedge clk)
        (color_depth_i == 2'b00) && (x_lsb_i == 2'b11) |-> (sel_o == 4'b0001) && (mem_o == {color_i[7:0]})
    );

// For color_depth_i==01 and x_lsb_i[0]==0, sel_o must be 1100 and mem_o must be {color_i[15:0], 16'h0000}.
    check_sel_mem_01_0: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b0) |-> (sel_o == 4'b1100) && (mem_o == {color_i[15:0], 16'h0000})
    );

// For color_depth_i==01 and x_lsb_i[0]==1, sel_o must be 0011 and mem_o must be {color_i[15:0]}.
    check_sel_mem_01_1: assert property (
        @(posedge clk)
        (color_depth_i == 2'b01) && (x_lsb_i[0] == 1'b1) |-> (sel_o == 4'b0011) && (mem_o == {color_i[15:0]})
    );

// For color_depth_i!=00, sel_o must be 1111 and mem_o must pass through color_i.
    check_sel_mem_default: assert property (
        @(posedge clk)
        (color_depth_i != 2'b00) |-> (sel_o == 4'b1111) && (mem_o == color_i)
    );

endmodule
