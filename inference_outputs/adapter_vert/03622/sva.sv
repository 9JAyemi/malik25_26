property ClockSynceotid; @(posedge clk_in_15) (key_in) |-> (key_15) ;endproperty 
 
 property KeySynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) |-> (key_14) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) |-> (key_13) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) |-> (key_12) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) |-> (key_11) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) |-> (key_10) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) |-> (key_9) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) |-> (key_8) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) |-> (key_7) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) |-> (key_6) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) |-> (key_5) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) |-> (key_4) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) |-> (key_3) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) &&  (  reg_10 ) |-> (key_2) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) &&  (  reg_10 ) &&  (  reg_9 ) |-> (key_1) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg