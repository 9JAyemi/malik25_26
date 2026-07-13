module barrel_shifter_sva (
    input logic clk,
    input logic in,
    input logic out1,
    input logic out2,
    input logic out
);

property ClockSynceotid; @(posedge clk) (in) |-> (out1 == in[7:0]) && (out2 == in[15:8]); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (in) |-> (out1) && (out2); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (in) |-> (out) == (in); endproperty
assert property (ClockSynceotid_3);

endmodule