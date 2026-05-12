property ResetSynceotid; @(negedge clk_reset_12) (mode) == (2'b00) |-> (out) == ({in[2:0], 1'b0}); endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_12) (mode) == (2'b01) |-> (out) == ({1'b0, in[3:1]}); endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_12) (mode) == (2'b10) |-> (out) == (~in); endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_12) (mode) == (2'b11) |-> (out) == (in); endproperty 
 
 property ResetSynceotid; (mode) != 2'b00 && (mode) != 2'b01 && (mode) != 2'b10 && (mode) != 2'b11 |-> (out) == 4'b0; endproperty 
 