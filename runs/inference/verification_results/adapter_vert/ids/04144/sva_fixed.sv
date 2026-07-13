module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic out,
    input logic sel,
    input logic b1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (b) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (a) ; endproperty
assert property (SyncIneotid);

endmodule