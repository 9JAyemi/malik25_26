module data_select_sva (
    input logic data,
    input logic sel,
    input logic temp_data,
    input logic x_axis,
    input logic y_axis,
    input logic z_axis,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1,
    input logic h00
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (data) == (x_axis) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (sel) == (2'b01) |-> (data) == (y_axis) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (sel) == (2'b10) |-> (data) == (z_axis) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (sel) == (2'b11) |-> (data) == ({8'h00, temp_data}) ; endproperty
assert property (ClockSynceotid_4);

endmodule