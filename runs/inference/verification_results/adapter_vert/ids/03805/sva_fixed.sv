module Test6_sva (
    input logic OE,
    input logic Z,
    input logic b01,
    input logic b1,
    input logic b10,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (OE) |-> (Z) == 2'b10 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (OE) != 1'b1  |-> (Z) == 2'b01; endproperty
assert property (ClockSynceotid_2);

endmodule