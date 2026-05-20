module velocityControlHdl_Reset_Delay_sva (
    input logic CLK_IN,
    input logic Constant1_out1,
    input logic In_Delay_out1,
    input logic Out,
    input logic Reset_Switch1_out1,
    input logic Reset_Switch_out1,
    input logic enb_1_2000_0,
    input logic reset,
    input logic b0
);

property ResetSynceotid; @(posedge CLK_IN) (reset) |-> In_Delay_out1 == 32'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge CLK_IN) (reset) && !(enb_1_2000_0) |-> In_Delay_out1 == Constant1_out1 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge CLK_IN) (reset) && (enb_1_2000_0) |-> In_Delay_out1 == Reset_Switch1_out1 ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge CLK_IN) ! (reset)  |-> Out == Reset_Switch_out1 ;endproperty
assert property (ResetSynceotid_4);

endmodule