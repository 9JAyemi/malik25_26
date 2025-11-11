// SVA for reg_module: concise, high-signal-coverage
module reg_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        wenb,
  input logic [7:0]  in_data,
  input logic [7:0]  reg_out
);
  default clocking cb @(posedge clk); endclocking

  // Track when $past is valid
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: controls known at sample
  a_ctrl_known: assert property (!$isunknown({reset, wenb})));

  // Reset effect: next cycle clears to 0
  a_reset_clear: assert property (reset |=> reg_out == 8'h00);

  // While reset held, output remains 0 (from second cycle of reset onward)
  a_reset_hold:  assert property (past_valid && reset && $past(reset) |-> reg_out == 8'h00);

  // Write loads next cycle (no spurious reset interference via disable iff)
  a_write_load:  assert property (disable iff (reset) past_valid && wenb |=> reg_out == $past(in_data));

  // Hold value when no write (and no reset)
  a_hold_no_wen: assert property (disable iff (reset) past_valid && !wenb |=> reg_out == $past(reg_out));

  // Any change must be caused by reset or write
  a_change_has_cause: assert property (past_valid && (reg_out != $past(reg_out)) |-> $past(reset) || $past(wenb));

  // Data quality: if writing, data must be known; if not writing, output must be known
  a_in_known_on_write:   assert property (disable iff (reset) wenb |-> !$isunknown(in_data));
  a_out_known_no_write:  assert property (disable iff (reset) !wenb |-> !$isunknown(reg_out));

  // Coverage
  c_reset:  cover property (reset |=> reg_out == 8'h00);
  c_write:  cover property (disable iff (reset) past_valid && wenb ##1 reg_out == $past(in_data));
  c_hold:   cover property (disable iff (reset) past_valid && !wenb ##1 reg_out == $past(reg_out));
  c_b2b_writes: cover property (disable iff (reset)
                                past_valid && wenb ##1 wenb && ($past(in_data) != in_data));
  c_reset_then_write: cover property (reset ##1 !reset [*1:$] ##1 wenb);
endmodule

// Bind into DUT
bind reg_module reg_module_sva u_reg_module_sva (
  .clk    (clk),
  .reset  (reset),
  .wenb   (wenb),
  .in_data(in_data),
  .reg_out(reg_out)
);