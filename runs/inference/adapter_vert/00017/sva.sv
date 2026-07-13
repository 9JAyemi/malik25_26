property ClockSynceotid; @(posedge clk_in_12) (n63) &&  (Z_B) |->  (N_1) ;endproperty 
 property SyncCheckeotid; @(posedge clk_in_12) (Z_B) &&  (n62) |->  (N_3) ;endproperty 
 property ValidDataeotid; @(posedge clk_in_12) (Ldir_int) &&  (N_8) &&  (Rdir_int) |->  (N_4) ;endproperty 
 property ValidDataeotid; @(posedge clk_in_12) (N_1) ||  (N_4) |->  (Len_int) ;endproperty 
 property ValidRuneotid; @(posedge clk_in_12) (N_4) ||  (N_3) |->  (Ren_int) ;endproperty 
 property ClockSynceotid; @(posedge clk_in_12) (n62) |->  (Rdir_int) != 1'b1 ;endproperty 
 property ClockSynceotid; @(posedge clk_in_12) (n63) |->  (Ldir_int) != 1'b1 ;endproperty 
 property SyncSafeeotid; @(posedge clk_in_12) (Z_B) |->  (N_8) != 1'b0 ;endproperty 
 