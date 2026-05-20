module dynamic_gate_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic b0,
    input logic b1
);

property ClockSynceotid; @(posedge clk) (in) |-> (out == 1'b1) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (in) != 1'b1  |-> (out == 1'b0) ; endproperty
assert property (ClockSynceotid_2);

endmodule