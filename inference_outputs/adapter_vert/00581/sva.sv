property ResetSynceotid; @(posedge clk) (  !reset_n  ) |->  pwm_timer == 0 && fifo_rdreq == 0 && audiodata_32 == 0 && audiodata_32_p == 0 && data_rdy == 0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  != 12'h800  ) |->  pwm_timer == pwm_timer + 1'b1 ;endproperty 
 
 property Readyeotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'h800  ) &&  (  fifo_empty != 0  ) |->  fifo_rdreq == 1'b1 ;endproperty 
 
 property Readyeotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'h801  ) &&  (  fifo_rdreq == 1  ) |->  fifo_rdreq == 0 && audiodata_32_p == fifo_data && data_rdy == 1'b1 ;endproperty 
 
 property SyncDataeotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'hfff  ) &&  (  data_rdy == 1  ) |->  audiodata_32 == audiodata_32_p && data_rdy == 0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  !reset_n  ) |->  pwm_out_l == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  !reset_n  ) |->  pwm_out_r == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  <= audiodata_32[15:4]  ) |->  pwm_out_l == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  > audiodata_32[15:4]  ) |->  pwm_out_l == 1'b0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  <= audiodata_32[31:20]  ) |->  pwm_out_r == 1'b1 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  > audiodata_32[31:20]  ) |->  pwm_out_r == 1'b0 ;endproperty 
 