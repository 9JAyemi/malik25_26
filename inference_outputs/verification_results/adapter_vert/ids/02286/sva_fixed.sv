module sysgen_logical_8b7810a2aa_sva (
    input logic clk,
    input logic d0,
    input logic d0_1_24,
    input logic d1,
    input logic d1_1_27,
    input logic fully_2_1_bit,
    input logic y
);

property ClockSynceotid; @(posedge clk) (d0) |-> (d0_1_24) ; endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk) (d1) |-> (d1_1_27) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (d0) ||  (d1) |-> (fully_2_1_bit) ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (d0) ||  (d1) |-> (y) ; endproperty
assert property (SyncCheckeotid_3);

endmodule