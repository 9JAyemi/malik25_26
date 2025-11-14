// SVA for shift_register
module shift_register_sva (
  input clk,
  input shift_enable,
  input parallel_load_enable,
  input [15:0] data_in,
  input [15:0] data_out
);

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Functional correctness
  ap_load:  assert property (parallel_load_enable |=> data_out == $past(data_in));
  ap_shift: assert property (!parallel_load_enable && shift_enable
                             |=> data_out == {$past(data_out)[14:0], 1'b0});
  ap_hold:  assert property (!parallel_load_enable && !shift_enable
                             |=> data_out == $past(data_out));

  // Priority when both enables high: load dominates shift
  ap_prio:  assert property (parallel_load_enable && shift_enable
                             |=> data_out == $past(data_in));

  // Bit-level consequence of shift: MSB comes from prev bit14, LSB becomes 0
  ap_shift_bits: assert property (!parallel_load_enable && shift_enable
                                  |=> data_out[15] == $past(data_out[14]) && data_out[0] == 1'b0);

  // Coverage
  cp_load:  cover property (parallel_load_enable);
  cp_shift: cover property (!parallel_load_enable && shift_enable);
  cp_hold:  cover property (!parallel_load_enable && !shift_enable);
  cp_both:  cover property (parallel_load_enable && shift_enable);
  cp_load_then_shift: cover property (parallel_load_enable ##1 (!parallel_load_enable && shift_enable));
  cp_3_shifts: cover property ((!parallel_load_enable && shift_enable)[*3]);
  cp_clear_by_16_shifts: cover property (parallel_load_enable && data_in != 16'h0000
                                         ##1 (!parallel_load_enable && shift_enable)[*16]
                                         ##1 data_out == 16'h0000);

endmodule

bind shift_register shift_register_sva sva_inst (.*);