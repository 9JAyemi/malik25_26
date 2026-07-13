property ResetSynceotid; @(posedge CLK_IN) (reset) |-> In_Delay_out1 == 32'b0 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK_IN) (reset) && !(enb_1_2000_0) |-> In_Delay_out1 == Constant1_out1 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK_IN) (reset) && (enb_1_2000_0) |-> In_Delay_out1 == Reset_Switch1_out1 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK_IN) ! (reset)  |-> Out == Reset_Switch_out1 ;endproperty 
 