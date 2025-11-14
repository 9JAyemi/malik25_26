// Bindable SVA for my_fpga_count_dn_1k
// Focused, concise checks + key coverage

bind my_fpga_count_dn_1k my_fpga_count_dn_1k_sva my_fpga_count_dn_1k_sva_i();

module my_fpga_count_dn_1k_sva;

  // Use DUT scope names directly via bind
  // Clock/reset policy
  default clocking cb @(posedge clk); endclocking
  default disable iff (n_rst); // active-high synchronous reset disables most checks

  // -----------------------
  // Reset behavior (must STILL fire while reset is asserted)
  // -----------------------
  assert property (disable iff (1'b0)
                   n_rst |-> (cnt_reg==32'd0
                           && cnt_1k_reg==4'd0
                           && cnt_1k_period==32'd0
                           && cnt_1k_period_reg==32'd0
                           && cnt_1k_divider==3'd0))
    else $error("Reset failed to clear all state to 0");

  // -----------------------
  // Sanity / structural checks
  // -----------------------
  // Outputs are 1-bit, must equal LSB of their driving regs
  assert property (cnt === cnt_reg[0])
    else $error("cnt != LSB of cnt_reg (width truncation mismatch)");
  assert property (cnt_1k === cnt_1k_reg[0])
    else $error("cnt_1k != LSB of cnt_1k_reg (width truncation mismatch)");

  // Known-ness on primary I/O when out of reset
  assert property (!$isunknown({dn,cnt,cnt_1k}))
    else $error("X/Z detected on I/O");

  // Invariant: min <= max (never inverted)
  assert property (cnt_1k_period_min <= cnt_1k_period_max)
    else $error("cnt_1k_period_min > cnt_1k_period_max");

  // -----------------------
  // cnt_reg behavior
  // -----------------------
  // cnt_reg increments by dn (0/1) each cycle out of reset
  assert property (cnt_reg == $past(cnt_reg) + $past(dn))
    else $error("cnt_reg does not increment by dn");

  // -----------------------
  // 1k period accumulation and capture
  // -----------------------
  // When period threshold reached or exceeded: wrap to 0, capture previous period
  assert property (($past(cnt_1k_period) >= $past(cnt_1k_period_max))
                   |-> (cnt_1k_period == 32'd0
                     && cnt_1k_period_reg == $past(cnt_1k_period)))
    else $error("cnt_1k_period wrap/capture incorrect");

  // Otherwise: period increments by 1 and capture reg is stable
  assert property (($past(cnt_1k_period) < $past(cnt_1k_period_max))
                   |-> (cnt_1k_period == $past(cnt_1k_period) + 32'd1
                     && $stable(cnt_1k_period_reg)))
    else $error("cnt_1k_period increment/stability incorrect");

  // -----------------------
  // Divider behavior
  // -----------------------
  localparam int DW = $bits(cnt_1k_divider);

  // If divider > 0, it must count down by 1
  assert property (($past(cnt_1k_divider) > 0)
                   |-> (cnt_1k_divider == $past(cnt_1k_divider) - {{(DW-1){1'b0}},1'b1}))
    else $error("cnt_1k_divider failed to decrement when > 0");

  // If divider == 0 and period threshold hit, it loads (increment from 0 by INC)
  assert property (($past(cnt_1k_divider) == 0
                    && $past(cnt_1k_period) >= $past(cnt_1k_period_max))
                   |-> (cnt_1k_divider == ($past(cnt_1k_divider)
                                           + $past(cnt_1k_divider_inc[DW-1:0]))))
    else $error("cnt_1k_divider failed to load from 0 when period hit");

  // If divider == 0 and period threshold not hit, it holds at 0
  assert property (($past(cnt_1k_divider) == 0
                    && $past(cnt_1k_period) < $past(cnt_1k_period_max))
                   |-> (cnt_1k_divider == 0))
    else $error("cnt_1k_divider changed unexpectedly while idle");

  // -----------------------
  // Intended 1 kHz “tick” side-effects (flag bug if absent)
  // On divider transition 1 -> 0, expect tick actions:
  //   - cnt_1k_reg updates to cnt_reg - cnt_1k_period_reg
  //   - cnt_1k_period_reg clears to 0
  //   - (side-effects on min/max may follow based on comparisons)
  // Current RTL never performs these due to unreachable condition; this assertion will expose that.
  // -----------------------
  assert property (($past(cnt_1k_divider)==3'd1 && cnt_1k_divider==3'd0)
                   |-> (cnt_1k_reg == $past(cnt_reg) - $past(cnt_1k_period_reg)
                     && cnt_1k_period_reg == 32'd0))
    else $error("Missing 1k tick side-effects on divider 1->0 transition");

  // -----------------------
  // Coverage
  // -----------------------
  // Period wrap event observed
  cover property ($past(cnt_1k_period) >= $past(cnt_1k_period_max)
                  && cnt_1k_period==0);

  // Divider zero -> nonzero load on period hit
  cover property ($past(cnt_1k_divider)==0
                  && $past(cnt_1k_period) >= $past(cnt_1k_period_max)
                  && cnt_1k_divider == $past(cnt_1k_divider) + $past(cnt_1k_divider_inc[DW-1:0]));

  // Divider 1 -> 0 (tick opportunity)
  cover property ($past(cnt_1k_divider)==3'd1 && cnt_1k_divider==3'd0);

  // Adaptive bounds adjustment attempts (should cover if tick side-effects occur)
  cover property (cnt_1k_reg > cnt_1k_period_max);
  cover property (cnt_1k_reg < cnt_1k_period_min);

endmodule