property ResetSynceotid; @(posedge clk) (reset) |-> counter == 64'b0000_0000_0000_0000_0000_0000_0000_0000 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) ( !reset ) |-> counter == {counter[62:0], counter[63] ^ counter[0]} ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !reset ) |-> output_val == counter & {64{input_val}} ;endproperty 
 