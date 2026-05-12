property ClockSynceotid; @(posedge src_clk) ( clk_en ) |-> ( clk_en_reg ) ; endproperty 
 
 property ClockSynceotid; @(posedge src_clk) ( clk_en ) &&  (  clk_en_reg  != clk_en ) |-> ( clk_en_13 ) ; endproperty 
 
 property ClockSynceotid; @(posedge src_clk) ( clk_en_13 ) &&  (  clk_en_14  != clk_en_13 ) |-> ( clk_en_15 ) ; endproperty 
 
 property ClockSynceotid; @(posedge src_clk) ( clk_en_15 ) &&  (  clk_en_16  != clk_en_15 ) |-> ( clk_11 ) ; endproperty 
 