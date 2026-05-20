module signal_processor_sva (
    input logic in,
    input logic out,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (in) |-> (out) == (in * 2) ; endproperty
assert property (ClockSynceotid);

property Squareeotid; @(posedge clk_in_14) (in) && ( in <= 7 ) |-> (out) == (in * in) ; endproperty
assert property (Squareeotid);

property DivBy2eotid; @(posedge clk_in_14) (in) &&  ( !(in < 4) && !(in <= 7)  )  |-> (out) == (in / 2) ; endproperty
assert property (DivBy2eotid);

endmodule