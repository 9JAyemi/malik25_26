module RCB_FRL_TrainingPattern_sva (
    input logic CLK,
    input logic DATA_OUT,
    input logic RST,
    input logic b1,
    input logic hc2,
    input logic hf4
);

property ResetSynceotid; @(posedge CLK) (RST) |-> DATA_OUT == 0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge CLK) (RST) != 1'b1 &&  (DATA_OUT) == 8'hf4  |->  (DATA_OUT) == 8'hc2 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge CLK) (RST) != 1'b1 &&  (DATA_OUT) != 8'hf4  |->  (DATA_OUT) == 8'hf4 ;endproperty
assert property (ResetSynceotid_3);

endmodule