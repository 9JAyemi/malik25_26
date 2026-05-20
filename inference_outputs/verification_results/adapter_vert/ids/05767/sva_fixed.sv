module xor_gate_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic mux_in,
    input logic out,
    input logic sel,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b1,
    input logic b10,
    input logic b11
);

property ClockSynceotid; @(posedge clk) (a) != (b) |-> (out) == 1'b1 ; endproperty
assert property (ClockSynceotid);

property SyncEqeotid; @(posedge clk) (a) == (b) |-> (out) == 1'b0 ; endproperty
assert property (SyncEqeotid);

property DataSynceotid; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  |->  (sel) != 2'b00 ; endproperty
assert property (DataSynceotid);

property SyncCheckeotid; @(posedge clk) (a) != (b) &&  (b) != (mux_in)  |->  (sel) != 2'b01 ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  &&  (b) != (mux_in)  |->  (sel) != 2'b10 ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (a) != (b) &&  (a) != (mux_in)  &&  (b) != (mux_in)  |->  (sel) == 2'b11 ; endproperty
assert property (SyncCheckeotid_3);

endmodule