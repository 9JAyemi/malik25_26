property ClockSynceotid; @(posedge slowest_sync_clk) (cnt_100M) == (100_000_000) |-> (Core) == 1 ;endproperty 
 
 property SyncCheckeotid; @(posedge slowest_sync_clk) (cnt_100M) != 100_000_000  |-> (Core) == 0 ;endproperty 
 
 property SyncCtrleotid; @(posedge lpf_int) (Core) &&  (cnt_core) == 2**8  |-> (bsr) == 1 ;endproperty 
 
 property SyncCtrleotid; @(posedge lpf_int) (Core) &&  (cnt_core) != 2**8  |-> (bsr) == 0 ;endproperty 
 
 property SyncCtrleotid; @(posedge lpf_int) (bsr) &&  (cnt_bsr) == 2**6  |-> (pr) == 1 ;endproperty 
 
 property SyncCtrleotid; @(posedge lpf_int) (bsr) &&  (cnt_bsr) != 2**6  |-> (pr) == 0 ;endproperty 
 