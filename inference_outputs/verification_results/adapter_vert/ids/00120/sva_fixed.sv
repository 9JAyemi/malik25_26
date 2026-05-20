module sky130_fd_sc_ms__a2111oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic Y,
    input logic clk_osc_19
);

property SyncCheckeotid; @(posedge clk_osc_19) (A1) && (A2) && (B1) && (C1) && (D1) |-> (Y) ; endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_osc_19) (A1) && (A2) && ! (B1) && (C1) && (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_19) (A1) && (A2) &&  (B1) && ! (C1) && (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_2);

property SyncSafeeotid_3; @(posedge clk_osc_19) (A1) && (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_3);

property SyncSafeeotid_4; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_4);

property SyncSafeeotid_5; @(posedge clk_osc_19) ! (A1) && ! (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_5);

property SyncSafeeotid_6; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_6);

property SyncSafeeotid_7; @(posedge clk_osc_19) ! (A1) && ! (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_7);

property SyncSafeeotid_8; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_8);

property SyncSafeeotid_9; @(posedge clk_osc_19) ! (A1) &&  (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_9);

property SyncSafeeotid_10; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_10);

property SyncSafeeotid_11; @(posedge clk_osc_19) ! (A1) &&  (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_11);

property SyncSafeeotid_12; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_12);

property SyncSafeeotid_13; @(posedge clk_osc_19)  (A1) && ! (A2) && ! (B1) &&  (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_13);

property SyncSafeeotid_14; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) && ! (C1) &&  (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_14);

property SyncSafeeotid_15; @(posedge clk_osc_19)  (A1) && ! (A2) &&  (B1) &&  (C1) && ! (D1) |-> (Y) ; endproperty
assert property (SyncSafeeotid_15);

endmodule