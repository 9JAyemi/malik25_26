property ResetSynceotid; @(posedge clk) (reset) |-> (out) == (4'b0) && (prev_in) == (4'b0); endproperty 
 
 property SyncChangeeotid; @(posedge clk) (reset) |-> (out) == (32'b0) && (prev_in) == (32'b0); endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in[3:0] != prev_in) |-> (out) == (in[3:0]) && (prev_in) == (in[3:0]); endproperty 
 
 property SyncChangeeotid; @(posedge clk) (in[35:4] != prev_in) |-> (out) == (prev_in & ~in[35:4]) && (prev_in) == (in[35:4]); endproperty 
 
 property SyncCheckeotid; @(posedge clk) (seq_out | change_out) |-> (final_out) == (seq_out | change_out); endproperty 
 