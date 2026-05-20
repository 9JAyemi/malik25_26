module FullAdder_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic ci,
    input logic co,
    input logic s,
    input logic sig_fa_0_a,
    input logic sig_fa_0_b,
    input logic sig_fa_0_ci,
    input logic sig_fa_1_a,
    input logic sig_fa_1_b,
    input logic sig_fa_1_ci,
    input logic sig_fa_1_co,
    input logic sig_fa_1_s,
    input logic sig_fa_3_a,
    input logic sig_fa_3_b,
    input logic sig_fa_3_ci,
    input logic sig_fa_3_co,
    input logic sig_fa_3_s,
    input logic clk_in_1,
    input logic sig_fa_2,
    input logic sig_fa_4_a,
    input logic sig_fa_4_b,
    input logic sig_fa_4_ci,
    input logic sig_fa_4_co,
    input logic sig_fa_4_s,
    input logic sig_fa_5_a,
    input logic sig_fa_5_b,
    input logic sig_fa_5_ci,
    input logic sig_fa_5_co,
    input logic sig_fa_5_s,
    input logic sig_fa_6_a,
    input logic sig_fa_6_b,
    input logic sig_fa_6_ci,
    input logic sig_fa_6_co,
    input logic sig_fa_6_s,
    input logic sig_fa_7_a,
    input logic sig_fa_7_b,
    input logic sig_fa_7_ci,
    input logic sig_fa_7_co,
    input logic sig_fa_7_s
);

property CarryOn; @(posedge clk_in_1) (a) |-> (sig_fa_0_a) ; endproperty
assert property (CarryOn);

property AddOneeotid; @(posedge clk_in_1) (b) |-> (sig_fa_0_b) ; endproperty
assert property (AddOneeotid);

property ValidInputeotid; @(posedge clk_in_1) (ci) |-> (sig_fa_0_ci) ; endproperty
assert property (ValidInputeotid);

property CarrySynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (co) ; endproperty
assert property (CarrySynceotid);

property AddOneeotid_2; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (s) ; endproperty
assert property (AddOneeotid_2);

property SyncAddereotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (SyncAddereotid);

property SyncAddereotid_2; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (SyncAddereotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (AddOneeotid_3);

property SyncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_1_a) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (b) |-> (sig_fa_1_b) ; endproperty
assert property (SyncCheckeotid_2);

property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_1_ci) ; endproperty
assert property (ncCheckeotid);

property yncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_1_co) ; endproperty
assert property (yncCheckeotid);

property yncCheckeotid_2; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_1_s) ; endproperty
assert property (yncCheckeotid_2);

property ncCheckeotid_2; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (sig_fa_2) ; endproperty
assert property (ncCheckeotid_2);

property ncCheckeotid_3; @(posedge clk_in_1) (sig_fa_2) |-> (co) ; endproperty
assert property (ncCheckeotid_3);

property ncCheckeotid_4; @(posedge clk_in_1) (sig_fa_2) |-> (s) ; endproperty
assert property (ncCheckeotid_4);

property ncCheckeotid_5; @(posedge clk_in_1) (a) |-> (sig_fa_3_a) ; endproperty
assert property (ncCheckeotid_5);

property ncCheckeotid_6; @(posedge clk_in_1) (b) |-> (sig_fa_3_b) ; endproperty
assert property (ncCheckeotid_6);

property ncCheckeotid_7; @(posedge clk_in_1) (c) |-> (sig_fa_3_ci) ; endproperty
assert property (ncCheckeotid_7);

property ncCheckeotid_8; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_3_co) ; endproperty
assert property (ncCheckeotid_8);

property ncCheckeotid_9; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_3_s) ; endproperty
assert property (ncCheckeotid_9);

property ncCheckeotid_10; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (ncCheckeotid_10);

property yncCheckeotid_3; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (yncCheckeotid_3);

property ncCheckeotid_11; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (ncCheckeotid_11);

property yncCheckeotid_4; @(posedge clk_in_1) (a) |-> (sig_fa_4_a) ; endproperty
assert property (yncCheckeotid_4);

property ncCheckeotid_12; @(posedge clk_in_1) (b) |-> (sig_fa_4_b) ; endproperty
assert property (ncCheckeotid_12);

property ncCheckeotid_13; @(posedge clk_in_1) (c) |-> (sig_fa_4_ci) ; endproperty
assert property (ncCheckeotid_13);

property ncCheckeotid_14; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_4_co) ; endproperty
assert property (ncCheckeotid_14);

property ncCheckeotid_15; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_4_s) ; endproperty
assert property (ncCheckeotid_15);

property ncCheckeotid_16; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (ncCheckeotid_16);

property yncCheckeotid_5; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (yncCheckeotid_5);

property ncCheckeotid_17; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (ncCheckeotid_17);

property yncCheckeotid_6; @(posedge clk_in_1) (a) |-> (sig_fa_5_a) ; endproperty
assert property (yncCheckeotid_6);

property ncCheckeotid_18; @(posedge clk_in_1) (b) |-> (sig_fa_5_b) ; endproperty
assert property (ncCheckeotid_18);

property ncCheckeotid_19; @(posedge clk_in_1) (c) |-> (sig_fa_5_ci) ; endproperty
assert property (ncCheckeotid_19);

property ncCheckeotid_20; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_5_co) ; endproperty
assert property (ncCheckeotid_20);

property ncCheckeotid_21; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_5_s) ; endproperty
assert property (ncCheckeotid_21);

property ncCheckeotid_22; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (ncCheckeotid_22);

property yncCheckeotid_7; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (yncCheckeotid_7);

property ncCheckeotid_23; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (ncCheckeotid_23);

property yncCheckeotid_8; @(posedge clk_in_1) (a) |-> (sig_fa_6_a) ; endproperty
assert property (yncCheckeotid_8);

property ncCheckeotid_24; @(posedge clk_in_1) (b) |-> (sig_fa_6_b) ; endproperty
assert property (ncCheckeotid_24);

property ncCheckeotid_25; @(posedge clk_in_1) (c) |-> (sig_fa_6_ci) ; endproperty
assert property (ncCheckeotid_25);

property ncCheckeotid_26; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_6_co) ; endproperty
assert property (ncCheckeotid_26);

property ncCheckeotid_27; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_6_s) ; endproperty
assert property (ncCheckeotid_27);

property ncCheckeotid_28; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (ncCheckeotid_28);

property yncCheckeotid_9; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (yncCheckeotid_9);

property ncCheckeotid_29; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (ncCheckeotid_29);

property yncCheckeotid_10; @(posedge clk_in_1) (a) |-> (sig_fa_7_a) ; endproperty
assert property (yncCheckeotid_10);

property ncCheckeotid_30; @(posedge clk_in_1) (b) |-> (sig_fa_7_b) ; endproperty
assert property (ncCheckeotid_30);

property ncCheckeotid_31; @(posedge clk_in_1) (c) |-> (sig_fa_7_ci) ; endproperty
assert property (ncCheckeotid_31);

property ncCheckeotid_32; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_7_co) ; endproperty
assert property (ncCheckeotid_32);

property ncCheckeotid_33; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_7_s) ; endproperty
assert property (ncCheckeotid_33);

property ncCheckeotid_34; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty
assert property (ncCheckeotid_34);

property yncCheckeotid_11; @(posedge clk_in_1) (c) |-> (co) ; endproperty
assert property (yncCheckeotid_11);

property ncCheckeotid_35; @(posedge clk_in_1) (c) |-> (s) ; endproperty
assert property (ncCheckeotid_35);

endmodule