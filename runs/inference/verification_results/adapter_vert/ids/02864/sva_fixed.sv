module mux2_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out,
    input logic sel,
    input logic b0
);

property ClockSynceotid; @(posedge clk) (sel) |-> (out == in2) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk) (sel) != 1'b0  |-> (out == in1) ; endproperty
assert property (SyncIneotid);

endmodule