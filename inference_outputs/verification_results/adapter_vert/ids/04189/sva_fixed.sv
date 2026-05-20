module shift_reg_sva (
    input logic CLK,
    input logic D,
    input logic LD,
    input logic RST,
    input logic reg1,
    input logic b0,
    input logic b1,
    input logic reg2,
    input logic reg3,
    input logic reg4
);

property ResetSynceotid; @(posedge CLK) (RST) |-> reg1 == 4'b0 && reg2 == 4'b0 && reg3 == 4'b0 && reg4 == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (LD) |-> reg1 == D && reg2 == reg1 && reg3 == reg2 && reg4 == reg3 ;endproperty
assert property (LoadSynceotid);

property SyncCheckeotid; @(posedge CLK) (RST) != 1'b1 &&  !(LD)  |-> reg1 == reg2 && reg2 == reg3 && reg3 == reg4 ;endproperty
assert property (SyncCheckeotid);

endmodule