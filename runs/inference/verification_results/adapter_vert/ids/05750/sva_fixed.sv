module mux_2_1_sva (
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y,
    input logic b1,
    input logic clk_in_13
);

property ClockSynceotid; @(posedge clk_in_13) (SEL) |-> (Y) == (B) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_13) (SEL) != 1'b1  |-> (Y) == (A) ; endproperty
assert property (SyncIneotid);

endmodule