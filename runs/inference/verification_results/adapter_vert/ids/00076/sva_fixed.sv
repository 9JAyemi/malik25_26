module barrel_shifter_sva (
    input logic A,
    input logic enable,
    input logic out,
    input logic select,
    input logic shift_amount,
    input logic shift_dir,
    input logic shifted_A,
    input logic b0,
    input logic b00,
    input logic b000,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1,
    input logic h0001,
    input logic h0002,
    input logic h0004,
    input logic h0008
);

property ShiftSynceotid; @(posedge clk_in_1) (shift_dir) |-> (shift_amount == 2'b00) && (A == shifted_A); endproperty
assert property (ShiftSynceotid);

property ShiftOneeotid; @(posedge clk_in_1) (shift_dir) && (shift_amount == 2'b01) |-> (shifted_A == {A[2:0], 1'b0}); endproperty
assert property (ShiftOneeotid);

property ShiftTwoeotid; @(posedge clk_in_1) (shift_dir) && (shift_amount == 2'b10) |-> (shifted_A == {A[1:0], 2'b00}); endproperty
assert property (ShiftTwoeotid);

property ShiftThreeseotid; @(posedge clk_in_1) (shift_dir) && (shift_amount != 2'b00) && (shift_amount != 2'b01) && (shift_amount != 2'b10) |-> (shifted_A == {A[0], 3'b000}); endproperty
assert property (ShiftThreeseotid);

property EnableSynceotid; @(posedge clk_in_1) (enable) && (select == 2'b00) |-> (out == 16'h0001); endproperty
assert property (EnableSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (enable) && (select == 2'b01) |-> (out == 16'h0002); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (enable) && (select == 2'b10) |-> (out == 16'h0004); endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (enable) && (select == 2'b11) |-> (out == 16'h0008); endproperty
assert property (ValidDataeotid_3);

property SafeSynceotid; @(posedge clk_in_1) ! (enable)  |-> (out == 16'b0); endproperty
assert property (SafeSynceotid);

endmodule