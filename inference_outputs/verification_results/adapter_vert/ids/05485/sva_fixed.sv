module mux2to1_sva (
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (SEL) |-> (Y) == (A) ; endproperty
assert property (ClockSynceotid);

property DataSynceotid; @(posedge clk_in_1) (SEL) != 0 |-> (Y) == (B) ; endproperty
assert property (DataSynceotid);

endmodule