// SVA for dct_processor
module dct_processor_sva (
  input logic               clk,
  // DUT inputs/outputs
  input logic [29:0]        dct_buffer,
  input logic [3:0]         dct_count,
  input logic               test_ending,
  input logic               test_has_ended, // unused by DUT; kept for coverage hookups if desired
  input logic [15:0]        current_coefficient,
  input logic [3:0]         total_coefficients,
  // DUT internals
  input logic [29:0]        dct_buffer_reg,
  input logic [3:0]         dct_count_reg,
  input logic [15:0]        current_coefficient_reg,
  input logic [3:0]         total_coefficients_reg,
  input logic               processing
);
  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Output wiring checks
  ap_out_tie: assert property (current_coefficient == current_coefficient_reg
                             && total_coefficients == total_coefficients_reg);

  // No X after first cycle
  ap_no_x: assert property (!$isunknown({processing,
                                         dct_buffer_reg, dct_count_reg,
                                         current_coefficient_reg, total_coefficients_reg,
                                         current_coefficient, total_coefficients})));

  // FSM behavior (priority: test_ending -> done on count==0 -> start on count>0)
  ap_fsm_testend: assert property ($past(test_ending) |-> processing == 1'b0);

  ap_fsm_done_on_zero: assert property (
    !$past(test_ending) && $past(processing) && ($past(dct_count_reg) == 4'd0)
    |-> processing == 1'b0
  );

  ap_fsm_start_on_gt0: assert property (
    !$past(test_ending) && !$past(processing) && ($past(dct_count_reg) > 4'd0)
    |-> processing == 1'b1
  );

  ap_fsm_hold_else: assert property (
    !$past(test_ending)
    && !($past(processing) && ($past(dct_count_reg) == 4'd0))
    && !((!$past(processing)) && ($past(dct_count_reg) > 4'd0))
    |-> processing == $past(processing)
  );

  // Non-processing cycle loads and clears
  ap_idle_loads: assert property (
    $past(processing) == 1'b0
    |-> ( current_coefficient_reg == 16'd0
       && dct_buffer_reg == $past(dct_buffer)
       && dct_count_reg  == $past(dct_count)
       && total_coefficients_reg == 4'd0)
  );

  // Processing cycle datapath updates
  ap_proc_updates: assert property (
    $past(processing) == 1'b1
    |-> ( current_coefficient_reg == $past(dct_buffer_reg[15:0])
       && dct_buffer_reg == { $past(dct_buffer_reg[14:0]), 1'b0 }
       && dct_count_reg  == ($past(dct_count_reg) - 4'd1) )
  );

  // Total coefficients update policy
  ap_total_inc_on_zero: assert property (
    $past(processing) == 1'b1 && ($past(dct_count_reg) == 4'd0)
    |-> total_coefficients_reg == ($past(total_coefficients_reg) + 4'd1)
  );

  ap_total_hold_else: assert property (
    $past(processing) == 1'b1 && ($past(dct_count_reg) != 4'd0)
    |-> total_coefficients_reg == $past(total_coefficients_reg)
  );

  // Basic covers (start, natural stop by count, forced stop by test_ending)
  cv_start: cover property (!$past(processing) && ($past(dct_count_reg) > 0) && !$past(test_ending) ##1 processing);

  cv_stop_by_zero: cover property ($past(processing) && ($past(dct_count_reg) == 0) ##1 !processing);

  cv_stop_by_testend: cover property (processing && test_ending ##1 !processing);

  // End-to-end run: start -> run -> stop by zero within a bounded window
  cv_run_e2e: cover property (
    !$past(processing) && ($past(dct_count_reg) > 0) && !$past(test_ending)
    ##1 processing
    ##[1:20] ($past(processing) && ($past(dct_count_reg) == 0) && !processing)
  );

endmodule

// Bind into DUT (accesses internal regs via hierarchical connects)
bind dct_processor dct_processor_sva sva_i (
  .clk                    (clk),
  .dct_buffer             (dct_buffer),
  .dct_count              (dct_count),
  .test_ending            (test_ending),
  .test_has_ended         (test_has_ended),
  .current_coefficient    (current_coefficient),
  .total_coefficients     (total_coefficients),
  .dct_buffer_reg         (dct_buffer_reg),
  .dct_count_reg          (dct_count_reg),
  .current_coefficient_reg(current_coefficient_reg),
  .total_coefficients_reg (total_coefficients_reg),
  .processing             (processing)
);