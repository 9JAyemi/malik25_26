// SVA for unsigned_non_restoring_divider
// Bind example:
// bind unsigned_non_restoring_divider unsigned_non_restoring_divider_sva #(.N(N)) u_div_sva (.*);

module unsigned_non_restoring_divider_sva #(parameter int N = 8) (
  input logic clk,
  input logic rst,
  input logic [N-1:0] dividend,
  input logic [N-1:0] divisor,
  input logic [N-1:0] quotient,
  input logic [N-1:0] remainder,

  // internal DUT regs (bind these by name)
  input logic [N-1:0] dividend_reg,
  input logic [N-1:0] divisor_reg,
  input logic [N-1:0] quotient_reg,
  input logic [N-1:0] remainder_reg,
  input logic [N-1:0] dividend_shift_reg,
  input logic [N:0]   counter_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic logic [N-1:0] bitmask(int idx);
    bitmask = '0;
    if (idx >= 0 && idx < N) bitmask = (logic[N-1:0]) (1 << idx);
  endfunction

  // Output mapping
  a_outputs_map: assert property (1'b1 |-> (quotient == quotient_reg && remainder == remainder_reg));

  // No X after reset deassert
  a_no_x: assert property (! $isunknown({quotient,remainder,quotient_reg,remainder_reg,dividend_reg,divisor_reg,dividend_shift_reg,counter_reg})));

  // Reset behavior
  a_reset_vals: assert property (rst |=> dividend_reg == '0 && divisor_reg == '0 && quotient_reg == '0 && remainder_reg == '0
                                      && dividend_shift_reg == {dividend,1'b0} && counter_reg == N+1);

  // Counter range and progress
  a_ctr_range:     assert property (counter_reg inside {[0:N+1]});
  a_ctr_progress:  assert property (($past(counter_reg) != 0) |-> (counter_reg == $past(counter_reg)-1));
  a_ctr_reload:    assert property (($past(counter_reg) == 0) |-> (counter_reg == N+1));

  // Prevent illegal bit index in 1<<(counter-1) update (catches design bug if counter goes to N+1)
  a_shift_index_in_range: assert property (($past(counter_reg) != 0) |-> ($past(counter_reg) <= N));

  // Pipeline register updates
  a_dividend_reg_upd: assert property (dividend_reg == $past(dividend_shift_reg[N-1:0]));
  a_divisor_reg_upd:  assert property (divisor_reg  == $past(divisor));

  // Remainder update per compare
  a_rem_update: assert property (($past(counter_reg) != 0) |->
                                 ( ($past(remainder_reg) >= $past(divisor_reg))
                                   ? (remainder_reg == $past(remainder_reg) - $past(divisor_reg))
                                   : (remainder_reg == $past(remainder_reg)) ));

  // Quotient update per compare
  a_quo_update_true: assert property (($past(counter_reg) != 0 && $past(remainder_reg) >= $past(divisor_reg)) |->
                                      (quotient_reg == ($past(quotient_reg) | bitmask($past(counter_reg)-1))));
  a_quo_update_false: assert property (($past(counter_reg) != 0 && $past(remainder_reg) <  $past(divisor_reg)) |->
                                       (quotient_reg == $past(quotient_reg)));

  // Reload behavior when counter==0
  a_reload: assert property (($past(counter_reg) == 0) |->
                             (remainder_reg == $past(dividend_shift_reg[N-1:0])
                              && quotient_reg == (($past(quotient_reg) << 1) | $past(dividend[N-1]))
                              && dividend_shift_reg == {dividend,1'b0}));

  // Golden functional check across a run (assumes stable inputs during run and divisor!=0)
  logic [N-1:0] start_dividend, start_divisor;
  logic run_active;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      start_dividend <= '0;
      start_divisor  <= '0;
      run_active     <= 1'b0;
    end else begin
      // detect reload/start: prev counter==0, now N+1
      if (counter_reg == N+1 && $past(counter_reg) == 0) begin
        start_dividend <= dividend;
        start_divisor  <= divisor;
        run_active     <= 1'b1;
      end
      // run completes when prev counter==1 (now 0)
      if ($past(counter_reg) == 1) begin
        run_active <= 1'b0;
      end
    end
  end

  // Assumptions for functional check (remove/relax if divide-by-zero is intended to be supported)
  as_inputs_stable_during_run: assume property (run_active |-> ($stable(dividend) && $stable(divisor)));
  as_divisor_nonzero:          assume property ((counter_reg == N+1 && $past(counter_reg) == 0) |-> (divisor != '0));

  // Check Euclidean division at end of run (just after last decrement: current counter==0 and $past==1)
  a_functional: assert property (($past(counter_reg) == 1) |->
                                 (quotient_reg  == (start_dividend / start_divisor)
                                  && remainder_reg == (start_dividend % start_divisor)));

  // Coverage
  c_take_true:  cover property ($past(counter_reg) != 0 && $past(remainder_reg) >= $past(divisor_reg));
  c_take_false: cover property ($past(counter_reg) != 0 && $past(remainder_reg) <  $past(divisor_reg));
  c_complete:   cover property ($past(counter_reg) == 1 && counter_reg == 0);
  c_reload:     cover property ($past(counter_reg) == 0 && counter_reg == N+1);
  c_div0_start: cover property ((counter_reg == N+1 && $past(counter_reg) == 0) && (divisor == '0));

endmodule