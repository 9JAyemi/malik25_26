// SVA for pwm: bind-in module with concise but comprehensive checks/coverage
module pwm_sva #(parameter MAX_WAVE = 24)
(
  input  logic                     clk,
  input  logic                     rst,
  input  logic [MAX_WAVE-1:0]      period,
  input  logic [MAX_WAVE-1:0]      compare,
  input  logic                     pwm,
  // internal regs (bound hierarchically)
  input  logic [MAX_WAVE-1:0]      ctr_q,
  input  logic [MAX_WAVE-1:0]      ctr_d,
  input  logic                     pwm_q,
  input  logic                     pwm_d
);

  default clocking cb @(posedge clk); endclocking

  // track when $past is valid
  logic past_valid;
  always_ff @(posedge clk) past_valid <= !rst && (past_valid || !rst);

  // Sanity: no X on registered outputs/counter (after reset)
  assert property (disable iff (rst) !$isunknown({pwm, pwm_q, ctr_q}));

  // Output net equals registered flop
  assert property (disable iff (rst) pwm == pwm_q);

  // Reset behavior: clears and holds while asserted
  assert property (rst |-> (ctr_q == '0 && pwm == 1'b0) throughout rst);

  // Counter next-state function
  assert property (past_valid |-> ctr_q ==
                   ( ($past(ctr_q) >= $past(period)) ? '0 : ($past(ctr_q) + 1) ));

  // Combinational next-value equations (catches bad sensitivity lists)
  assert property (ctr_d == ((ctr_q >= period) ? '0 : (ctr_q + 1))));
  assert property (pwm_d == (compare > ctr_d));

  // PWM equals compare against next counter (uses prior-cycle compare)
  assert property (past_valid |-> pwm == ($past(compare) > ctr_q));

  // Duty-cycle extremes (derived from relation, but asserted explicitly)
  assert property (past_valid && ($past(compare) == '0) |-> !pwm);
  assert property (past_valid && ($past(compare) > $past(period)) |-> pwm);

  // Coverage
  cover property (past_valid && ($past(ctr_q) >= $past(period)) && ctr_q == '0); // wrap
  cover property (past_valid && !pwm && $rose(pwm)); // low->high
  cover property (past_valid && pwm && $fell(pwm));  // high->low
  cover property (past_valid && ($past(compare) == '0) && !pwm);                // 0% duty
  cover property (past_valid && ($past(compare) > $past(period)) && pwm);       // 100% duty

endmodule

// Bind into DUT
bind pwm pwm_sva #(.MAX_WAVE(MAX_WAVE)) pwm_sva_i (
  .clk     (clk),
  .rst     (rst),
  .period  (period),
  .compare (compare),
  .pwm     (pwm),
  .ctr_q   (ctr_q),
  .ctr_d   (ctr_d),
  .pwm_q   (pwm_q),
  .pwm_d   (pwm_d)
);