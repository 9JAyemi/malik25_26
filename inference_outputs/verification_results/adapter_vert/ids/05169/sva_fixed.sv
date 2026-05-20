module sequence_counter_sva (
    input logic Core,
    input logic bsr,
    input logic cnt_100M,
    input logic cnt_bsr,
    input logic cnt_core,
    input logic lpf_int,
    input logic pr,
    input logic slowest_sync_clk
);

property ClockSynceotid; @(posedge slowest_sync_clk) (cnt_100M) == (100_000_000) |-> (Core) == 1 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge slowest_sync_clk) (cnt_100M) != 100_000_000  |-> (Core) == 0 ;endproperty
assert property (SyncCheckeotid);

property SyncCtrleotid; @(posedge lpf_int) (Core) &&  (cnt_core) == 2**8  |-> (bsr) == 1 ;endproperty
assert property (SyncCtrleotid);

property SyncCtrleotid_2; @(posedge lpf_int) (Core) &&  (cnt_core) != 2**8  |-> (bsr) == 0 ;endproperty
assert property (SyncCtrleotid_2);

property SyncCtrleotid_3; @(posedge lpf_int) (bsr) &&  (cnt_bsr) == 2**6  |-> (pr) == 1 ;endproperty
assert property (SyncCtrleotid_3);

property SyncCtrleotid_4; @(posedge lpf_int) (bsr) &&  (cnt_bsr) != 2**6  |-> (pr) == 0 ;endproperty
assert property (SyncCtrleotid_4);

endmodule