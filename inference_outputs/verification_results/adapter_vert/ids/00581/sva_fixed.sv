module pwm_out_sva (
    input logic audiodata_32,
    input logic clk,
    input logic data_rdy,
    input logic fifo_data,
    input logic fifo_empty,
    input logic fifo_rdreq,
    input logic pwm_out_l,
    input logic pwm_out_r,
    input logic pwm_timer,
    input logic reset_n,
    input logic audiodata_32_p,
    input logic b0,
    input logic b1,
    input logic h800,
    input logic h801,
    input logic hfff
);

property ResetSynceotid; @(posedge clk) (  !reset_n  ) |->  pwm_timer == 0 && fifo_rdreq == 0 && audiodata_32 == 0 && audiodata_32_p == 0 && data_rdy == 0 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  != 12'h800  ) |->  pwm_timer == pwm_timer + 1'b1 ;endproperty
assert property (ClockSynceotid);

property Readyeotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'h800  ) &&  (  fifo_empty != 0  ) |->  fifo_rdreq == 1'b1 ;endproperty
assert property (Readyeotid);

property Readyeotid_2; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'h801  ) &&  (  fifo_rdreq == 1  ) |->  fifo_rdreq == 0 && audiodata_32_p == fifo_data && data_rdy == 1'b1 ;endproperty
assert property (Readyeotid_2);

property SyncDataeotid; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  == 12'hfff  ) &&  (  data_rdy == 1  ) |->  audiodata_32 == audiodata_32_p && data_rdy == 0 ;endproperty
assert property (SyncDataeotid);

property ClockSynceotid_2; @(posedge clk) (  !reset_n  ) |->  pwm_out_l == 1'b1 ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (  !reset_n  ) |->  pwm_out_r == 1'b1 ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  <= audiodata_32[15:4]  ) |->  pwm_out_l == 1'b1 ;endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  > audiodata_32[15:4]  ) |->  pwm_out_l == 1'b0 ;endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  <= audiodata_32[31:20]  ) |->  pwm_out_r == 1'b1 ;endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk) (  reset_n  ) &&  (  pwm_timer  > audiodata_32[31:20]  ) |->  pwm_out_r == 1'b0 ;endproperty
assert property (ClockSynceotid_7);

endmodule