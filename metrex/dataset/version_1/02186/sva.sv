// SVA for clk_synchronizer
// Bind this checker to the DUT. Focused, high-signal-coverage, concise.

module clk_synchronizer_sva #(
  parameter longint unsigned SYSCLK_FREQ_HZ   = 64'd100_000_000,
  parameter longint unsigned PPS_HIGH_LEVEL_US= 64'd10_000,
  parameter longint unsigned GENCLK_FREQ_HZ   = 1,
  parameter int unsigned     FORWARD_OFFSET_CLK = 0
)(
  input  logic clk,
  input  logic rst_n,
  input  logic pps_in,
  input  logic sync_clk_out,
  input  logic clk_sync_ok_out
);

  // Recompute key constants locally for assertions
  localparam longint unsigned SVA_DUTY_CNT_N  = (SYSCLK_FREQ_HZ * PPS_HIGH_LEVEL_US) / 64'd1_000_000;
  localparam longint unsigned SVA_DIVIDER_NUM = (GENCLK_FREQ_HZ == 0) ? 0 : (SYSCLK_FREQ_HZ / GENCLK_FREQ_HZ);

  // Default clocking/disable
  clocking cb @(posedge clk); endclocking
  default clocking cb;
  default disable iff (!rst_n);

  // Parameter/legal-range checks (time 0)
  initial begin
    assert (SYSCLK_FREQ_HZ > 0) else $error("SYSCLK_FREQ_HZ must be > 0");
    assert (GENCLK_FREQ_HZ  > 0) else $error("GENCLK_FREQ_HZ must be > 0");
    assert (SVA_DIVIDER_NUM > 0) else $error("DIVIDER_NUM must be > 0");
    assert (SVA_DUTY_CNT_N <= SVA_DIVIDER_NUM) else $error("DUTY_CNT_N must be <= DIVIDER_NUM");
    assert (FORWARD_OFFSET_CLK + 2 < SVA_DIVIDER_NUM) else $error("FORWARD_OFFSET_CLK+2 must be < DIVIDER_NUM");
  end

  // ========= Structural equivalences =========
  // Internal equivalences
  assert property (rst_release == (rst_pps || clk_sync_flag));
  assert property (rst_pps_rst == (rst_release || !rst_n));

  // Output wiring equivalences
  assert property (clk_sync_ok_out == clk_sync_flag);
  assert property (sync_clk_out    == clk_generated);

  // Generated clock gating behavior
  assert property (clk_generated == (clk_sync_flag ? clk_gen_forward : 1'b0));

  // ========= Reset behavior =========
  assert property (@(posedge clk) !rst_n |-> (rst_release==0 && clk_sync_flag==0 && clk_generated==0));

  // ========= rst_pps (async set/clear) =========
  // rst_pps must clear on rst_pps_rst posedge
  assert property (@(posedge rst_pps_rst) rst_pps==0);
  // rst_pps must set on pps_in posedge when not being held in reset
  assert property (@(posedge pps_in) disable iff (!rst_n || rst_pps_rst) rst_pps==1);

  // ========= clk_sync_flag properties =========
  // Sets when rst_release rises
  assert property ($rose(rst_release) |=> clk_sync_flag);
  // Once high, it never falls until reset
  assert property (!$fell(clk_sync_flag));

  // ========= Divider counter correctness =========
  // Range
  assert property (clk_divider < SVA_DIVIDER_NUM);
  // Count +1 when not wrapping and no async load active
  assert property ( (!rst_pps && $past(!rst_pps)) && ($past(clk_divider) < SVA_DIVIDER_NUM-1)
                    |=> clk_divider == ($past(clk_divider)+1) );
  // Wrap to 0 from terminal count when no async load active
  assert property ( (!rst_pps && $past(!rst_pps)) && ($past(clk_divider) == SVA_DIVIDER_NUM-1)
                    |=> clk_divider == '0 );
  // Async load value on rst_pps posedge
  assert property (@(posedge rst_pps) clk_divider == (FORWARD_OFFSET_CLK + 2));

  // ========= PWM generation correctness =========
  // Combinational mapping
  assert property (clk_gen_forward == (clk_divider < SVA_DUTY_CNT_N));

  // ========= X checks (when out of reset) =========
  assert property (!$isunknown({clk_sync_ok_out, sync_clk_out, clk_gen_forward, clk_generated,
                                rst_release, clk_sync_flag, clk_divider}));

  // ========= Useful coverage =========
  // Achieve lock
  cover property ($rose(clk_sync_flag));
  // Observe one full period shape after lock and no async load
  cover property ( (!rst_pps && clk_sync_flag && clk_divider==0)
                   ##1 (clk_gen_forward [*SVA_DUTY_CNT_N])
                   ##1 (!clk_gen_forward [*(SVA_DIVIDER_NUM - SVA_DUTY_CNT_N)])
                   ##1 (clk_divider==0) );
  // Divider wrap
  cover property ( (!rst_pps) && $past(clk_divider)==SVA_DIVIDER_NUM-1 && clk_divider==0 );
  // Async load observed
  cover property (@(posedge rst_pps) clk_divider == (FORWARD_OFFSET_CLK + 2));

endmodule

// Bind to the DUT
bind clk_synchronizer
  clk_synchronizer_sva #(
    .SYSCLK_FREQ_HZ(SYSCLK_FREQ_HZ),
    .PPS_HIGH_LEVEL_US(PPS_HIGH_LEVEL_US),
    .GENCLK_FREQ_HZ(GENCLK_FREQ_HZ),
    .FORWARD_OFFSET_CLK(FORWARD_OFFSET_CLK)
  ) clk_synchronizer_sva_i (
    .clk(clk),
    .rst_n(rst_n),
    .pps_in(pps_in),
    .sync_clk_out(sync_clk_out),
    .clk_sync_ok_out(clk_sync_ok_out)
  );