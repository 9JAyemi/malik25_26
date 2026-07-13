module MUX4_1_SL_sva (
    input logic S0,
    input logic S1,
    input logic S2,
    input logic S3,
    input logic Sel,
    input logic out,
    input logic b00,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (Sel) == (2'b11) |-> (out) == (S3) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (Sel) != 2'b11 &&  (Sel) == 2'b10  |-> (out) == (S2) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (Sel) != 2'b11 &&  (Sel) != 2'b10  |-> (out) == (S0) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (Sel) == 2'b00  |-> (out) == (S1) ; endproperty
assert property (ClockSynceotid_4);

endmodule