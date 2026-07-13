property ResetSynceotid; @(posedge CLK) (reset) |-> out == 4'd0 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) (reset) |-> out != in1 + in2 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) !reset |-> out == in1 + in2 ;endproperty 
 