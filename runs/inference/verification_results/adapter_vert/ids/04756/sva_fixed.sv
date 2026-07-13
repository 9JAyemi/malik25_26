module shift_register_sva (
    input logic CLK,
    input logic CLR,
    input logic D1,
    input logic LD1,
    input logic Q1,
    input logic sum,
    input logic D2,
    input logic LD2,
    input logic b0000,
    input logic b1
);

property ResetSynceotid; @(posedge CLK) (CLR) |-> (Q1) == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge CLK) (CLR) != 1'b1 && (LD1) |-> (Q1) ==  (D1) ;endproperty
assert property (LoadSynceotid);

property ShiftSynceotid; @(posedge CLK) (CLR) != 1'b1 && !(LD1)  |-> (Q1) ==  ({Q1[2:0], Q1[3]}) ;endproperty
assert property (ShiftSynceotid);

property SyncAddereotid; @(posedge CLK) (CLR)  &&  (LD1)  &&  (LD2) |->  (sum) ==  (D1 + D2) ;endproperty
assert property (SyncAddereotid);

property SyncCheckeotid; @(posedge CLK) (CLR)  &&  (LD1)  &&  !(LD2) |->  (Q1) ==  (D1) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge CLK) (CLR)  &&  !(LD1)  &&  (LD2) |->  (Q1) ==  ({Q1[2:0], Q1[3]}) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge CLK) (CLR)  &&  !(LD1)  &&  !(LD2)  |->  (Q1) ==  4'b0000 ;endproperty
assert property (SyncCheckeotid_3);

endmodule