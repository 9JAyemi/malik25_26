// SVA for sd_clock_divider
// Bind-friendly checker that reaches internal regs
module sd_clock_divider_sva (
  input  logic        CLK,
  input  logic        RST,
  input  logic [7:0]  DIVIDER,
  input  logic        SD_CLK,
  input  logic [7:0]  ClockDiv,
  input  logic        SD_CLK_O
);

  default clocking cb @(posedge CLK); endclocking

  // Basic sanity
  a_no_x:         assert property (cb) disable iff (RST) !$isunknown({SD_CLK,ClockDiv,SD_CLK_O});
  a_out_match_in: assert property (cb) SD_CLK == SD_CLK_O;

  // Reset behavior (async assert, sync check)
  a_reset_hold:   assert property (cb) RST |-> (ClockDiv==8'h00 && SD_CLK==1'b0 && $stable(ClockDiv) && $stable(SD_CLK));
  a_reset_next:   assert property (cb) $rose(RST) |-> (ClockDiv==8'h00 && SD_CLK==1'b0);

  // Functional behavior (use past with reset to avoid X-startup)
  // Increment when not matching divider
  a_inc_else: assert property (cb) disable iff (RST)
    ($past(!RST,1,RST) && ($past(ClockDiv,1,RST) != $past(DIVIDER,1,RST)))
      |-> (ClockDiv == ($past(ClockDiv,1,RST)+8'h1) && SD_CLK == $past(SD_CLK,1,RST));

  // Toggle and reset counter on match
  a_toggle_on_match: assert property (cb) disable iff (RST)
    ($past(!RST,1,RST) && ($past(ClockDiv,1,RST) == $past(DIVIDER,1,RST)))
      |-> (ClockDiv == 8'h00 && SD_CLK != $past(SD_CLK,1,RST));

  // No spurious toggles
  a_only_toggle_when_match: assert property (cb) disable iff (RST)
    (SD_CLK != $past(SD_CLK,1,RST)) |-> ($past(ClockDiv,1,RST) == $past(DIVIDER,1,RST));

  // Optional: divider==0 => toggle every cycle, counter stays 0
  a_div0_every_cycle: assert property (cb) disable iff (RST)
    ($past(DIVIDER,1,RST)==8'h00) |-> (ClockDiv==8'h00 && SD_CLK != $past(SD_CLK,1,RST));

  // Coverage
  c_toggle:            cover property (cb) disable iff (RST) (SD_CLK != $past(SD_CLK,1,RST));
  c_two_toggles:       cover property (cb) disable iff (RST) (SD_CLK != $past(SD_CLK,1,RST)) ##[1:$] (SD_CLK != $past(SD_CLK,1,RST));
  c_midchange_divider: cover property (cb) disable iff (RST)
                         $changed(DIVIDER) ##[1:10] (SD_CLK != $past(SD_CLK,1,RST));
  // Wrap without toggle (e.g., DIVIDER != 8'hFF and ClockDiv wraps 0->...->FF->00)
  c_wrap_no_toggle:    cover property (cb) disable iff (RST)
                         ($past(ClockDiv,1,RST)==8'hFF && $past(DIVIDER,1,RST)!=8'hFF)
                         ##1 (ClockDiv==8'h00 && SD_CLK==$past(SD_CLK,1,RST));

endmodule

// Bind into DUT (connect internals)
bind sd_clock_divider sd_clock_divider_sva u_sd_clock_divider_sva (
  .CLK      (CLK),
  .RST      (RST),
  .DIVIDER  (DIVIDER),
  .SD_CLK   (SD_CLK),
  .ClockDiv (ClockDiv),
  .SD_CLK_O (SD_CLK_O)
);