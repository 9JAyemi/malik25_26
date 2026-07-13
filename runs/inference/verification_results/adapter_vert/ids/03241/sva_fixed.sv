module clock_gate_high_sva (
    input logic EN,
    input logic I,
    input logic O,
    input logic SE,
    input logic ECK,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (EN) |-> (ECK) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_15) (EN) &&  ( ! (SE) ) |-> (O) == (I) ;endproperty
assert property (ClockSynceotid_2);

endmodule