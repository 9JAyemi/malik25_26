module mux4to1_32_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic o,
    input logic sel,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (o) == (a) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (sel) == (2'b01) |-> (o) == (b) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (sel) == (2'b10) |-> (o) == (c) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (sel) == (2'b11) |-> (o) == (d) ; endproperty
assert property (ClockSynceotid_4);

endmodule