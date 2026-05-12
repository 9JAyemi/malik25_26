property ClockSynceotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b00) |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b00) |-> sel_o == 4'b1000 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b01) |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b01) |-> sel_o == 4'b0100 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b10) |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b10) |-> sel_o == 4'b0010 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b11) |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b11) |-> sel_o == 4'b0001 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b0)  |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b0)  |-> sel_o == 4'b1100 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b1)  |-> mem_o == color_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b1)  |-> sel_o == 4'b0011 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b00) |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b00) |-> sel_o == 4'b0001 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b01) |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b01) |-> sel_o == 4'b0011 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b10) |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b10) |-> sel_o == 4'b0011 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b11) |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b11) |-> sel_o == 4'b1111 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b0)  |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b0)  |-> sel_o == 4'b1100 ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b1)  |-> color_o == mem_i; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b1)  |-> sel_o == 4'b0011 ; endproperty 
 
 endmodule
 