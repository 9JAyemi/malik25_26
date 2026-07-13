module barrel_shifter_sva (
    input logic data,
    input logic result,
    input logic shift_amount,
    input logic b0000,
    input logic b0000000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic clk_in_15
);

property ShiftSynceotid; @(posedge clk_in_15) (shift_amount) == (4'b0000) |-> (result) == (data) ; endproperty
assert property (ShiftSynceotid);

property ShiftOneeotid; @(posedge clk_in_15) (shift_amount) == (4'b0001) |-> (result) == (data[2:0] & 7'b0000000) ; endproperty
assert property (ShiftOneeotid);

property ShiftTwoeotid; @(posedge clk_in_15) (shift_amount) == (4'b0010) |-> (result) == (data[1:0] & 7'b0000000) ; endproperty
assert property (ShiftTwoeotid);

property ShiftOneeotid_2; @(posedge clk_in_15) (shift_amount) == (4'b0011) |-> (result) == (data[0] & 7'b0000000) ; endproperty
assert property (ShiftOneeotid_2);

endmodule