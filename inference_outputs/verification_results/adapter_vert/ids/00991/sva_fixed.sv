module barrel_shifter_sva (
    input logic data_in,
    input logic data_out,
    input logic shift_amount,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_15
);

property ShiftSynceotid; @(posedge clk_in_15) (shift_amount) == (2'b00) |-> data_out == data_in ; endproperty
assert property (ShiftSynceotid);

property ShiftOneeotid; @(posedge clk_in_15) (shift_amount) == (2'b01) |-> data_out == data_in ; endproperty
assert property (ShiftOneeotid);

property ShiftTwoeotid; @(posedge clk_in_15) (shift_amount) == (2'b10) |-> data_out == data_in ; endproperty
assert property (ShiftTwoeotid);

property ShiftSynceotid_2; @(posedge clk_in_15) (shift_amount) != 2'b00 && (shift_amount) != 2'b01 && (shift_amount) != 2'b10  |-> data_out == data_in ; endproperty
assert property (ShiftSynceotid_2);

endmodule