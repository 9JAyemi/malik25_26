module adder_16bit_sva (
    input logic a,
    input logic b,
    input logic sum,
    input logic clk_in_1,
    input logic core_15,
    input logic core_16
);

property AdderSynceotid; @(posedge clk_in_1) (a) |-> (sum) ; endproperty
assert property (AdderSynceotid);

property SyncAddereotid; @(posedge clk_in_1) (b) |-> (sum) ; endproperty
assert property (SyncAddereotid);

property SyncAddereotid_2; @(posedge clk_in_1) (a) &&  (b) &&  (  !core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_2);

property SyncAddereotid_3; @(posedge clk_in_1) (a) &&  (  !b ) &&  (  !core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_3);

property SyncAddereotid_4; @(posedge clk_in_1) (  !a ) &&  (b) &&  (  !core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_4);

property SyncAddereotid_5; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  !core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_5);

property SyncAddereotid_6; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_6);

property SyncAddereotid_7; @(posedge clk_in_1) (  !a ) &&  (b) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_7);

property SyncAddereotid_8; @(posedge clk_in_1) (a) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_8);

property SyncAddereotid_9; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_9);

property SyncAddereotid_10; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_10);

property SyncAddereotid_11; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_11);

property SyncAddereotid_12; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_12);

property SyncAddereotid_13; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_13);

property SyncAddereotid_14; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_14);

property SyncAddereotid_15; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_15);

property SyncAddereotid_16; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_16);

property SyncAddereotid_17; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_17);

property SyncAddereotid_18; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_18);

property SyncAddereotid_19; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_19);

property SyncAddereotid_20; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_20);

property SyncAddereotid_21; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_21);

property SyncAddereotid_22; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_22);

property SyncAddereotid_23; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_23);

property SyncAddereotid_24; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_24);

property SyncAddereotid_25; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_25);

property SyncAddereotid_26; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_26);

property SyncAddereotid_27; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_27);

property SyncAddereotid_28; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_28);

property SyncAddereotid_29; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_29);

property SyncAddereotid_30; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_30);

property SyncAddereotid_31; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_31);

property SyncAddereotid_32; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_32);

property SyncAddereotid_33; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_33);

property SyncAddereotid_34; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_34);

property SyncAddereotid_35; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_35);

property SyncAddereotid_36; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_36);

property SyncAddereotid_37; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_37);

property SyncAddereotid_38; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_38);

property SyncAddereotid_39; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_39);

property SyncAddereotid_40; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_40);

property SyncAddereotid_41; @(posedge clk_in_1) (  !a ) &&  (  !b ) &&  (  core_15 ) |->  (  core_16 ) ; endproperty
assert property (SyncAddereotid_41);

endmodule