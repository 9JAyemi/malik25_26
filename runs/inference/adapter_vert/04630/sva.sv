property ResetSynceotid; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( cnt == 0 ) ;endproperty 
 
 property ResetSynceotid; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( clk2 == 1'b0 ) ;endproperty 
 
 property ResetSynceotid; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( wb_tgc_o == 1'b0 ) ;endproperty 
 