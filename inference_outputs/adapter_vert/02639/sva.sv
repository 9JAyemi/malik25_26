property ResetSynceotid; @(posedge clk) (reset) |-> dout == 0 ;endproperty 
 
 property ValidCeotid; @(posedge clk) (ce) && !(reset) |-> dout == dout + din0 * din1 ;endproperty 
 