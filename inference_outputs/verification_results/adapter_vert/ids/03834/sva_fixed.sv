module barrel_shifter_sva (
    input logic A,
    input logic D,
    input logic S,
    input logic b0,
    input logic b00,
    input logic b000,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_15
);

property ShiftSynceotid; @(posedge clk_in_15) (A) == (2'b00) |-> (S) == (D) ; endproperty
assert property (ShiftSynceotid);

property ShiftOneeotid; @(posedge clk_in_15) (A) == (2'b01) |-> (S) == ({D[2:0], 1'b0}) ; endproperty
assert property (ShiftOneeotid);

property ShiftTwoeotid; @(posedge clk_in_15) (A) == (2'b10) |-> (S) == ({D[1:0], 2'b00}) ; endproperty
assert property (ShiftTwoeotid);

property ShiftOneeotid_2; @(posedge clk_in_15) (A) == (2'b11) |-> (S) == ({D[0], 3'b000}) ; endproperty
assert property (ShiftOneeotid_2);

endmodule