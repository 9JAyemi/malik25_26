module mux4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b0,
    input logic b00,
    input logic b1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (in1) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (in0) ; endproperty
assert property (SyncIneotid);

property SyncMuxeotid; @(posedge clk_in_1) (sel) != 1'b0  && @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (in2) ; endproperty
assert property (SyncMuxeotid);

property SyncMuxeotid_2; @(posedge clk_in_1) (sel) == 2'b00  |-> (out) == (in3) ; endproperty
assert property (SyncMuxeotid_2);

endmodule