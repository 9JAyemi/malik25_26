module errman_nfl_sva (
  input logic clk,
  input logic rst, // active-high async reset
  input logic cfg_err_cpl_timeout_n,
  input logic decr_nfl,
  input logic nfl_num,
  input logic inc_dec_b
);

  ///// Reset behavior /////
  // While reset is asserted, outputs are held LOW.
  reset_outputs_low: assert property (
    @(posedge clk) rst |-> (nfl_num == 1'b0) && (inc_dec_b == 1'b0)
  );

  ///// Sequential behavior of nfl_num /////
  // nfl_num toggles every active clock (one-cycle complement).
  check_nfl_num_toggle_each_cycle: assert property (
    @(posedge clk) disable iff (rst) $past(1'b1) |-> (nfl_num == ~$past(nfl_num))
  );
  // nfl_num must change on every active clock edge.
  check_nfl_num_always_changes: assert property (
    @(posedge clk) disable iff (rst) $past(1'b1) |-> $changed(nfl_num)
  );

  ///// Registered capture of inc_dec_b /////
  // inc_dec_b equals NAND of inputs from the previous cycle (when previous cycle not in reset).
  check_inc_dec_b_captures_prev_nand: assert property (
    @(posedge clk) disable iff (rst) $past(!rst) |-> inc_dec_b == ~( $past(cfg_err_cpl_timeout_n) & $past(decr_nfl) )
  );
  // Any change on inc_dec_b reflects a change in previous-cycle NAND of inputs.
  check_inc_dec_b_change_matches_prev_input_change: assert property (
    @(posedge clk) disable iff (rst)
      $past(!rst,1) && $past(!rst,2) && $changed(inc_dec_b)
      |-> ($past(~(cfg_err_cpl_timeout_n & decr_nfl),1) != $past(~(cfg_err_cpl_timeout_n & decr_nfl),2))
  );
  // If previous-cycle NAND of inputs is unchanged, inc_dec_b does not change.
  check_inc_dec_b_no_change_if_prev_input_nand_unchanged: assert property (
    @(posedge clk) disable iff (rst)
      $past(!rst,1) && $past(!rst,2) && ($past(~(cfg_err_cpl_timeout_n & decr_nfl),1) == $past(~(cfg_err_cpl_timeout_n & decr_nfl),2))
      |-> !$changed(inc_dec_b)
  );

  ///// Consistency checks for inc_dec_b values /////
  // inc_dec_b can be 0 only if both inputs were 1 in the previous cycle.
  check_inc_dec_b_zero_only_on_prev_both_high: assert property (
    @(posedge clk) disable iff (rst) ($past(!rst) && (inc_dec_b == 1'b0)) |-> ($past(cfg_err_cpl_timeout_n) && $past(decr_nfl))
  );
  // inc_dec_b is 1 if at least one previous input was 0.
  check_inc_dec_b_one_on_prev_not_both_high: assert property (
    @(posedge clk) disable iff (rst) ($past(!rst) && (inc_dec_b == 1'b1)) |-> !($past(cfg_err_cpl_timeout_n) && $past(decr_nfl))
  );

endmodule