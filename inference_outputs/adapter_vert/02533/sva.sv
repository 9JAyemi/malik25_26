property ResetSynceotid; @(posedge clk_reset_17) (select) == (2'b00) |-> data_out == 7'b0000000 ; endproperty 
 
 property ResetSynceotid; @(posedge clk_reset_17) (select) == (2'b01) |-> data_out == ch_0 ; endproperty 
 
 property ResetSynceotid; @(posedge clk_reset_17) (select) == (2'b10) |-> data_out == ch_1 ; endproperty 
 
 property ResetSynceotid; @(posedge clk_reset_17) (select) == (2'b11) |-> data_out == ch_2 ; endproperty 
 