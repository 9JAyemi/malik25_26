module mux4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (out) == (in0) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (sel) == (2'b01) |-> (out) == (in1) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (sel) == (2'b10) |-> (out) == (in2) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (sel) == (2'b11) |-> (out) == (in3) ; endproperty
assert property (ClockSynceotid_4);

endmodule