// SVA for low_pass_filter
// Bindable checker that verifies synchronization, reset behavior, shift/sum update,
// lpf_int mapping, and corner-case coverage.

module low_pass_filter_sva (
  input  logic              slowest_sync_clk,
  input  logic              dcm_locked,
  input  logic              ext_reset_in,
  input  logic              mb_debug_sys_rst,
  input  logic              aux_reset_in,
  input  logic [4:0]        lpf_int,

  // Internal DUT signals (connected via bind)
  input  logic              sync_ext_reset_in,
  input  logic              sync_mb_debug_sys_rst,
  input  logic              sync_aux_reset_in,
  input  logic              sync_dcm_locked,
  input  logic              sync_reset,
  input  logic [15:0]       shift_reg,
  input  logic [15:0]       sum
);

  default clocking cb @(posedge slowest_sync_clk); endclocking

  bit past_valid;
  always_ff @(posedge slowest_sync_clk) past_valid <= 1'b1;

  // Synchronizers are 1-cycle samples of async inputs
  assert property (disable iff (!past_valid)
                   sync_ext_reset_in == $past(ext_reset_in));
  assert property (disable iff (!past_valid)
                   sync_mb_debug_sys_rst == $past(mb_debug_sys_rst));
  assert property (disable iff (!past_valid)
                   sync_aux_reset_in == $past(aux_reset_in));
  assert property (disable iff (!past_valid)
                   sync_dcm_locked == $past(dcm_locked));

  // sync_reset is the OR of synchronized resets
  assert property (sync_reset == (sync_ext_reset_in
                                  || sync_mb_debug_sys_rst
                                  || sync_aux_reset_in));

  // Reset clears state next cycle
  assert property (sync_reset |=> (shift_reg == 16'h0 && sum == 16'h0 && lpf_int == 5'h0));

  // Normal update: shift and running sum
  assert property (disable iff (!past_valid)
                   !sync_reset |=> ( shift_reg == { $past(shift_reg)[14:0], $past(sync_dcm_locked) }
                                   && sum      ==  $past(sum) + $past(sync_dcm_locked) - $past(shift_reg[0]) ));

  // Invariant: sum equals popcount of shift_reg and is in range
  assert property (sum == $countones(shift_reg));
  assert property (sum <= 16);

  // Output matches lower 5 bits of sum
  assert property (lpf_int == sum[4:0]);

  // External reset assertion forces zeroed output within two clocks
  assert property (disable iff (!past_valid)
                   $rose(ext_reset_in || mb_debug_sys_rst || aux_reset_in)
                   |-> ##2 (shift_reg == 16'h0 && sum == 16'h0 && lpf_int == 5'h0));

  // Output is never X/Z when clocking
  assert property (!$isunknown(lpf_int));

  // Coverage: see reset effect
  cover property (disable iff (!past_valid)
                  $rose(ext_reset_in || mb_debug_sys_rst || aux_reset_in)
                  ##2 (sum==0 && lpf_int==0));

  // Coverage: fill with 16 ones and reach max sum
  cover property ((!sync_reset && sync_dcm_locked)[*16] ##1 (sum==16 && lpf_int==5'd16));

  // Coverage: fill with 16 zeros and reach min sum
  cover property ((!sync_reset && !sync_dcm_locked)[*16] ##1 (sum==0 && lpf_int==5'd0));

  // Coverage: reach a mid value
  cover property (sum==16'd8 && !sync_reset);

endmodule

// Bind into the DUT (connects by name, including internals)
bind low_pass_filter low_pass_filter_sva sva_inst (.*);