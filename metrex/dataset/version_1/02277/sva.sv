// SVA for rx_control_data_rdy
module rx_control_data_rdy_sva(
  input        posedge_clk,
  input        rx_resetn,

  input        rx_error_c,
  input        rx_error_d,

  input [2:0]  control,
  input [2:0]  control_l_r,

  input        is_control,
  input [5:0]  counter_neg,
  input        last_is_control,

  input        rx_error,
  input        ready_control_p_r,
  input        ready_data_p_r,
  input        rx_got_fct_fsm
);

  default clocking cb @(posedge posedge_clk); endclocking
  default disable iff (!rx_resetn);

  // Handy past-cycle conditions
  let ctrl_ready_p = ($past(counter_neg) == 6'd4)  && $past(is_control);
  let data_ready_p = ($past(counter_neg) == 6'd32);
  let fct_cond_p   = ($past(control_l_r) != 3'd7)  && ($past(control) == 3'd4) && $past(last_is_control);

  // Asynchronous reset drives all outputs low immediately
  assert property (@(negedge rx_resetn) 1'b1 |-> ##0 (!rx_got_fct_fsm && !ready_control_p_r && !ready_data_p_r && !rx_error));

  // rx_error mirrors OR of error inputs (registered)
  assert property ($past(rx_resetn) |-> rx_error == ($past(rx_error_c) | $past(rx_error_d)));

  // Ready signal decode (registered)
  assert property (ctrl_ready_p |-> ( ready_control_p_r && !ready_data_p_r));
  assert property (data_ready_p |-> (!ready_control_p_r &&  ready_data_p_r));
  assert property ((!ctrl_ready_p && !data_ready_p) |-> (!ready_control_p_r && !ready_data_p_r));
  assert property (!(ready_control_p_r && ready_data_p_r)); // mutual exclusion

  // rx_got_fct_fsm set/hold behavior
  assert property (fct_cond_p |-> rx_got_fct_fsm);                 // set when condition seen
  assert property ($rose(rx_got_fct_fsm) |-> fct_cond_p);          // only set by the condition
  assert property (!$fell(rx_got_fct_fsm));                        // never clears while out of reset
  assert property ((!fct_cond_p && !$past(rx_got_fct_fsm)) |-> !rx_got_fct_fsm); // holds 0 otherwise

  // Coverage
  cover property ($rose(rx_resetn));
  cover property (ctrl_ready_p ##1 ready_control_p_r);
  cover property (data_ready_p ##1 ready_data_p_r);
  cover property ((!ctrl_ready_p && !data_ready_p) ##1 (!ready_control_p_r && !ready_data_p_r));
  cover property ($rose(rx_got_fct_fsm));
  cover property ($rose(rx_error));

endmodule

// Bind into the DUT
bind rx_control_data_rdy rx_control_data_rdy_sva u_rx_control_data_rdy_sva(.*);