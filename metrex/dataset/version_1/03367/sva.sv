// SVA for shift_register
module shift_register_sva (
  input clk,
  input load,
  input shift,
  input [3:0] data_in,
  input [3:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Next-state functional correctness
  assert property (load |=> data_out == $past(data_in));
  assert property ((shift && !load) |=> data_out == { $past(data_out)[2:0], 1'b0 });
  assert property ((!load && !shift) |=> data_out == $past(data_out));
  // Priority when both asserted
  assert property ((load && shift) |=> data_out == $past(data_in));
  // Output changes only if enabled
  assert property ($changed(data_out) |-> $past(load || shift));
  // Multi-cycle shift equivalence (sanity for sequencing)
  assert property ((shift && !load)[*2] |=> data_out == { $past(data_out,2)[1:0], 2'b00 });

  // Basic reachability coverage
  cover property (load);
  cover property (shift && !load);
  cover property (!load && !shift);
  cover property (load && shift);
  // Load followed by four shifts
  cover property (load ##1 (shift && !load)[*4]);
endmodule

// Bind to DUT
bind shift_register shift_register_sva u_shift_register_sva (
  .clk(clk),
  .load(load),
  .shift(shift),
  .data_in(data_in),
  .data_out(data_out)
);