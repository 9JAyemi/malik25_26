module color_to_memory_sva (
    input logic color_depth_i,
    input logic color_i,
    input logic color_o,
    input logic mem_i,
    input logic mem_lsb_i,
    input logic mem_o,
    input logic sel_o,
    input logic x_lsb_i,
    input logic b0,
    input logic b00,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b01,
    input logic b0100,
    input logic b1,
    input logic b10,
    input logic b1000,
    input logic b11,
    input logic b1100,
    input logic b1111,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b00) |-> mem_o == color_i; endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b00) |-> sel_o == 4'b1000 ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b01) |-> mem_o == color_i; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b01) |-> sel_o == 4'b0100 ; endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b10) |-> mem_o == color_i; endproperty
assert property (ValidDataeotid_4);

property ValidDataeotid_5; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b10) |-> sel_o == 4'b0010 ; endproperty
assert property (ValidDataeotid_5);

property ValidDataeotid_6; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b11) |-> mem_o == color_i; endproperty
assert property (ValidDataeotid_6);

property ValidDataeotid_7; @(posedge clk_in_1) (color_depth_i) == (2'b00) && (x_lsb_i) == (2'b11) |-> sel_o == 4'b0001 ; endproperty
assert property (ValidDataeotid_7);

property ValidDataeotid_8; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b0)  |-> mem_o == color_i; endproperty
assert property (ValidDataeotid_8);

property ValidDataeotid_9; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b0)  |-> sel_o == 4'b1100 ; endproperty
assert property (ValidDataeotid_9);

property ValidDataeotid_10; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b1)  |-> mem_o == color_i; endproperty
assert property (ValidDataeotid_10);

property ValidDataeotid_11; @(posedge clk_in_1) (color_depth_i) == (2'b01) && (x_lsb_i[0]) == (1'b1)  |-> sel_o == 4'b0011 ; endproperty
assert property (ValidDataeotid_11);

property ValidDataeotid_12; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b00) |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_12);

property ValidDataeotid_13; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b00) |-> sel_o == 4'b0001 ; endproperty
assert property (ValidDataeotid_13);

property ValidDataeotid_14; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b01) |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_14);

property ValidDataeotid_15; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b01) |-> sel_o == 4'b0011 ; endproperty
assert property (ValidDataeotid_15);

property ValidDataeotid_16; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b10) |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_16);

property ValidDataeotid_17; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b10) |-> sel_o == 4'b0011 ; endproperty
assert property (ValidDataeotid_17);

property ValidDataeotid_18; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b11) |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_18);

property ValidDataeotid_19; @(posedge clk_in_1) (color_depth_i) != 2'b00 && (mem_lsb_i) == (2'b11) |-> sel_o == 4'b1111 ; endproperty
assert property (ValidDataeotid_19);

property ValidDataeotid_20; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b0)  |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_20);

property ValidDataeotid_21; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b0)  |-> sel_o == 4'b1100 ; endproperty
assert property (ValidDataeotid_21);

property ValidDataeotid_22; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b1)  |-> color_o == mem_i; endproperty
assert property (ValidDataeotid_22);

property ValidDataeotid_23; @(posedge clk_in_1) (color_depth_i) != 2'b01 && (mem_lsb_i[0]) == (1'b1)  |-> sel_o == 4'b0011 ; endproperty
assert property (ValidDataeotid_23);

endmodule