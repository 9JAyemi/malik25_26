property ResetSynceotid; @(negedge clk) (rst_n) |-> rat == 8'b00000000 ;endproperty 
 
 property ResetSynceotid; @(negedge clk) (rst_n) |-> pc == 8'b00000000 ;endproperty 
 
 property ResetSynceotid; @(negedge clk) (rst_n) &&  (ld_rat == 1'b1) |-> rat == low_sum ;endproperty 
 
 property ResetSynceotid; @(negedge clk) (rst_n) &&  (ld_rat == 1'b1) |-> pc == pc_plus_one ;endproperty 
 
 property ResetSynceotid; @(negedge clk) (pc_at) == (1'b0) |-> m_at == pc ;endproperty 
 
 property ResetSynceotid; @(negedge clk) (pc_at) != 1'b0  |-> m_at == rat ;endproperty 
 
 