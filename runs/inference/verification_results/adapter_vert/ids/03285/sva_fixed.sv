module johnson_counter_sva (
    input logic clk,
    input logic q,
    input logic reset,
    input logic b000,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> (q) == (3'b000) ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) (reset) != 1'b1 |-> (q) == (q << 1) ;endproperty
assert property (ClockSynceotid);

endmodule