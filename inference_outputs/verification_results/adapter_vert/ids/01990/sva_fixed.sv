module FullAdder_sva (
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (AddOneeotid);

property SyncEqeotid; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid);

property SyncEqeotid_2; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_2);

property SyncEqeotid_3; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_3);

property SyncEqeotid_4; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_4);

property SyncEqeotid_5; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_5);

property SyncEqeotid_6; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_6);

property SyncEqeotid_7; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_7);

property SyncEqeotid_8; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_8);

property SyncEqeotid_9; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_9);

property SyncEqeotid_10; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_10);

property SyncEqeotid_11; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_11);

property SyncEqeotid_12; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_12);

property SyncEqeotid_13; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_13);

property SyncEqeotid_14; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_14);

property SyncEqeotid_15; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_15);

property SyncEqeotid_16; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_16);

property SyncEqeotid_17; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_17);

property SyncEqeotid_18; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_18);

property SyncEqeotid_19; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_19);

property SyncEqeotid_20; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_20);

property SyncEqeotid_21; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_21);

property SyncEqeotid_22; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_22);

property SyncEqeotid_23; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_23);

property SyncEqeotid_24; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_24);

property SyncEqeotid_25; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_25);

property SyncEqeotid_26; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_26);

property SyncEqeotid_27; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_27);

property SyncEqeotid_28; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_28);

property SyncEqeotid_29; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_29);

property SyncEqeotid_30; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_30);

property SyncEqeotid_31; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_31);

property SyncEqeotid_32; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_32);

property SyncEqeotid_33; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_33);

property SyncEqeotid_34; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_34);

property SyncEqeotid_35; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_35);

property SyncEqeotid_36; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_36);

property SyncEqeotid_37; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_37);

property SyncEqeotid_38; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_38);

property SyncEqeotid_39; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_39);

property SyncEqeotid_40; @(posedge clk_in_1) (A) != (B) && (Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_40);

property SyncEqeotid_41; @(posedge clk_in_1) (A) != (B) && !(Ci) |-> (S) != (A) && (S) != (B); endproperty
assert property (SyncEqeotid_41);

property SyncEqeotid_42; @(posedge clk_in_1) (A) == (B) && (Ci) |-> (S) == (A) && (S) != (B); endproperty
assert property (SyncEqeotid_42);

property SyncEqeotid_43; @(posedge clk_in_1) (A) == (B) && !(Ci) |-> (S) != (A) && (S) == (B); endproperty
assert property (SyncEqeotid_43);

endmodule