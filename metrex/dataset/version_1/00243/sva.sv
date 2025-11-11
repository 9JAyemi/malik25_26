// SVA for DDC and DUC
// Concise, high-signal-coverage checks with essential covers

// -------------- DDC assertions --------------
module DDC_sva (
  input clk,
  input reset,
  input [15:0] data_in,
  input [31:0] freq,
  input [7:0]  dec_factor,
  input [15:0] data_out,
  input [31:0] out_freq,
  input [15:0] filtered_data,
  input [31:0] counter
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  // Synchronous reset state
  assert property (@(posedge clk) reset |-> (filtered_data==16'h0 && counter==32'h0 && data_out==16'h0));

  // Filter update: y <= (x + y)>>1 using previous values
  assert property ($past(!reset) |-> filtered_data == (($past(data_in) + $past(filtered_data)) >> 1));

  // Counter increments or wraps; data_out updates only on wrap to previous filtered_data
  assert property ((counter == dec_factor - 1) |=> (counter==32'h0 && data_out == $past(filtered_data)));
  assert property ((counter != dec_factor - 1) |=> (counter == $past(counter) + 1 && data_out == $past(data_out)));

  // No divide-by-zero allowed; out_freq matches integer division
  assert property (dec_factor != 8'h0);
  assert property ((dec_factor != 8'h0) |-> (out_freq == (freq / dec_factor)));

  // No X on key regs/outs when active; allow out_freq X only when dec_factor==0 (already asserted prohibited)
  assert property (!$isunknown({filtered_data, counter, data_out})));
  assert property ((dec_factor != 8'h0) |-> !$isunknown(out_freq));

  // Basic covers
  cover property (dec_factor!=0 && counter==dec_factor-1 ##1 counter==0 && data_out==$past(filtered_data));
  cover property (dec_factor==8'd1 && counter==0 ##1 counter==0 ##1 counter==0); // always-sample case
endmodule

bind DDC DDC_sva ddc_sva_i (.*);

// -------------- DUC assertions --------------
module DUC_sva (
  input clk,
  input reset,
  input [15:0] data_in,
  input [31:0] freq,
  input [7:0]  interp_factor,
  input [15:0] data_out,
  input [31:0] out_freq,
  input [15:0] upsampled_data,
  input [31:0] counter
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  // Synchronous reset state
  assert property (@(posedge clk) reset |-> (counter==32'h0 && upsampled_data==16'h0 && data_out==16'h0));

  // Upsampler: strobe cycles capture data_in (prev), otherwise zero; counter inc/wrap
  assert property ((counter == interp_factor - 1) |=> (counter==32'h0 && upsampled_data == $past(data_in)));
  assert property ((counter != interp_factor - 1) |=> (counter == $past(counter) + 1 && upsampled_data == 16'h0));

  // Filter update: y <= (u + y)>>1 using previous values
  assert property ($past(!reset) |-> data_out == (($past(upsampled_data) + $past(data_out)) >> 1));

  // Output frequency relationship
  assert property (out_freq == (freq * interp_factor));

  // No X on key regs/outs when active
  assert property (!$isunknown({upsampled_data, counter, data_out, out_freq})));

  // Basic covers
  cover property (counter==interp_factor-1 ##1 counter==0 && upsampled_data==$past(data_in));
  cover property (interp_factor==8'd1 && counter==0 ##1 counter==0 ##1 counter==0); // always-strobe case
endmodule

bind DUC DUC_sva duc_sva_i (.*);