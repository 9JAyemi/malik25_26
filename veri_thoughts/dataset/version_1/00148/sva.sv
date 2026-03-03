// SVA for adc_fifo
module adc_fifo_sva
  #(parameter [7:0] RP_ID = 8'hA0)
(
  input  logic         clk,
  input  logic [31:0]  control,
  input  logic [31:0]  status,
  input  logic         src_adc_enable,
  input  logic         src_adc_valid,
  input  logic [15:0]  src_adc_data,
  input  logic         dst_adc_enable,
  input  logic         dst_adc_valid,
  input  logic [15:0]  dst_adc_data
);

  logic f_past_valid;
  always_ff @(posedge clk) f_past_valid <= 1'b1;

  // Constant/status checks
  ap_status_const:  assert property (@(posedge clk) status == {24'h0, RP_ID});
  ap_status_stable: assert property (@(posedge clk) disable iff (!f_past_valid) $stable(status));

  // 1-cycle pipeline behavior
  ap_en_pipe:   assert property (@(posedge clk) disable iff (!f_past_valid) dst_adc_enable == $past(src_adc_enable));
  ap_val_pipe:  assert property (@(posedge clk) disable iff (!f_past_valid) dst_adc_valid  == $past(src_adc_valid));
  ap_data_pipe: assert property (@(posedge clk) disable iff (!f_past_valid) dst_adc_data   == $past(src_adc_data));

  // Knownness propagation (no X on outputs if past input was known)
  ap_en_no_x:   assert property (@(posedge clk) disable iff (!f_past_valid) !$isunknown($past(src_adc_enable)) |-> !$isunknown(dst_adc_enable));
  ap_val_no_x:  assert property (@(posedge clk) disable iff (!f_past_valid) !$isunknown($past(src_adc_valid))  |-> !$isunknown(dst_adc_valid));
  ap_data_no_x: assert property (@(posedge clk) disable iff (!f_past_valid) !$isunknown($past(src_adc_data))   |-> !$isunknown(dst_adc_data));

  // Causality: output changes only due to prior-cycle input changes
  ap_en_change_cause:   assert property (@(posedge clk) disable iff (!f_past_valid || !$past(f_past_valid)) $changed(dst_adc_enable) |-> $past($changed(src_adc_enable)));
  ap_val_change_cause:  assert property (@(posedge clk) disable iff (!f_past_valid || !$past(f_past_valid)) $changed(dst_adc_valid)  |-> $past($changed(src_adc_valid)));
  ap_data_change_cause: assert property (@(posedge clk) disable iff (!f_past_valid || !$past(f_past_valid)) $changed(dst_adc_data)   |-> $past($changed(src_adc_data)));

  // Coverage: demonstrate 1-cycle latency and data pass-through
  cv_valid_latency:  cover property (@(posedge clk) f_past_valid && src_adc_valid  ##1 dst_adc_valid);
  cv_enable_latency: cover property (@(posedge clk) f_past_valid && src_adc_enable ##1 dst_adc_enable);
  cv_data_sample:    cover property (@(posedge clk) f_past_valid && src_adc_data == 16'hA55A ##1 dst_adc_data == 16'hA55A);
  cv_status_const:   cover property (@(posedge clk) status == {24'h0, RP_ID});

endmodule

// Bind into DUT
bind adc_fifo adc_fifo_sva #(.RP_ID(8'hA0)) adc_fifo_sva_i (.*);