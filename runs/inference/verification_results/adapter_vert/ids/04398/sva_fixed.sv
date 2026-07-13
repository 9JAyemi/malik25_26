module Sec6_SM_sva (
    input logic clk_i,
    input logic reset_n,
    input logic sel,
    input logic state,
    input logic state_next,
    input logic S0,
    input logic S1,
    input logic S2,
    input logic S3,
    input logic b000
);

property ResetSynceotid; @(posedge clk_i) (reset_n) |-> (state) == (S0) ; endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge clk_i) (reset_n) |-> (state) == (state_next) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_i) (reset_n) |-> (sel) == 3'b000 ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_i) (reset_n) &&  (  (state) == (S0)  ) |-> (state_next) == (S1) ; endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_i) (reset_n) &&  (  (state) == (S1)  ) |-> (state_next) == (S2) ; endproperty
assert property (SyncCheckeotid_4);

property SyncCheckeotid_5; @(posedge clk_i) (reset_n) &&  (  (state) == (S2)  ) |-> (state_next) == (S3) ; endproperty
assert property (SyncCheckeotid_5);

property SyncCheckeotid_6; @(posedge clk_i) (reset_n) &&  (  (state) == (S3)  ) |-> (state_next) == (S0) ; endproperty
assert property (SyncCheckeotid_6);

endmodule