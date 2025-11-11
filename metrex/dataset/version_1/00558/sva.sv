// SVA for register_ctrl_top
// Bind this module to the DUT: 
//   bind register_ctrl_top register_ctrl_top_sva u_register_ctrl_top_sva(.dut);

module register_ctrl_top_sva (register_ctrl_top dut);

  default clocking cb @(posedge dut.I_sys_clk); endclocking
  default disable iff (dut.I_sys_rst);

  // Reset behavior (checked during reset)
  a_reset_outputs_low: assert property (@(posedge dut.I_sys_clk)
    dut.I_sys_rst |-> (dut.O_usb_uart_rx_req==0 && dut.O_usb_uart_tx_req==0 &&
                       dut.O_usb_uart_tx_data==8'h00 && dut.O_usb_dir==0 &&
                       dut.O_motor_start==0 && dut.tp==0));

  // RX path
  a_rx_req_def:          assert property (dut.O_usb_uart_rx_req == (dut.I_usb_uart_rx_empty==1'b0));
  a_rx_d1_past_req:      assert property (dut.R_usb_uart_rx_req_d1 == $past(dut.O_usb_uart_rx_req));
  a_rx_en_past_req:      assert property (dut.R_rx_en == $past(dut.O_usb_uart_rx_req));
  a_rx_data_sample:      assert property (dut.R_rx_en |-> (dut.R_rx_data == dut.I_usb_uart_rx_data));

  // TX path
  a_tx_req_cond:         assert property (dut.O_usb_uart_tx_req |-> (!dut.I_usb_uart_tx_full && dut.I_key_start));
  a_tx_when_allowed:     assert property ((!dut.I_usb_uart_tx_full && dut.I_key_start) |-> (dut.O_usb_uart_tx_req && dut.O_usb_uart_tx_data==8'h55));
  a_tx_data_const_while_req: assert property (dut.O_usb_uart_tx_req |-> (dut.O_usb_uart_tx_data==8'h55));
  a_no_tx_when_full:     assert property (dut.I_usb_uart_tx_full |-> !dut.O_usb_uart_tx_req);

  // USB dir and motor control (effects visible next cycle)
  a_dir_to_0_on_00:      assert property ((dut.R_rx_en && dut.R_rx_data==8'h00) |=> dut.O_usb_dir==1'b0);
  a_dir_to_1_on_ff:      assert property ((dut.R_rx_en && dut.R_rx_data==8'hff) |=> dut.O_usb_dir==1'b1);
  a_dir_hold_other:      assert property ((dut.R_rx_en && (dut.R_rx_data!=8'h00) && (dut.R_rx_data!=8'hff)) |=> dut.O_usb_dir==$past(dut.O_usb_dir));

  a_motor_set_on_02:     assert property ((dut.R_rx_en && dut.R_rx_data==8'h02) |=> dut.O_motor_start==1'b1);
  a_motor_clear_when_no_rx: assert property ((!dut.R_rx_en) |=> dut.O_motor_start==1'b0);

  // Direction changes must be caused by correct command in prior cycle
  a_dir_change_cause_up:   assert property (( dut.O_usb_dir && !$past(dut.O_usb_dir)) |-> $past(dut.R_rx_en && dut.R_rx_data==8'hff));
  a_dir_change_cause_down: assert property ((!dut.O_usb_dir &&  $past(dut.O_usb_dir)) |-> $past(dut.R_rx_en && dut.R_rx_data==8'h00));

  // tp definition equivalence
  a_tp_def:              assert property (dut.tp == (dut.R_rx_en & (~(&dut.R_rx_data)) & dut.O_motor_start & dut.O_usb_dir));

  // No X on key outputs after reset released
  a_no_x_outputs:        assert property (!$isunknown({dut.O_usb_uart_tx_req,
                                                      dut.O_usb_uart_tx_data,
                                                      dut.O_usb_uart_rx_req,
                                                      dut.O_usb_dir,
                                                      dut.O_motor_start,
                                                      dut.tp})));

  // Coverage
  c_rx_to_en:   cover property ((dut.I_usb_uart_rx_empty==0) ##1 dut.R_rx_en);
  c_cmd_00:     cover property ((dut.I_usb_uart_rx_empty==0) ##1 (dut.R_rx_en && dut.R_rx_data==8'h00) ##1 (dut.O_usb_dir==0));
  c_cmd_ff:     cover property ((dut.I_usb_uart_rx_empty==0) ##1 (dut.R_rx_en && dut.R_rx_data==8'hff) ##1 (dut.O_usb_dir==1));
  c_cmd_02:     cover property ((dut.I_usb_uart_rx_empty==0) ##1 (dut.R_rx_en && dut.R_rx_data==8'h02) ##1 (dut.O_motor_start==1) ##1 (!dut.R_rx_en && dut.O_motor_start==0));
  c_tx:         cover property ((!dut.I_usb_uart_tx_full && dut.I_key_start) ##0 (dut.O_usb_uart_tx_req && dut.O_usb_uart_tx_data==8'h55));
  c_tp_hi:      cover property (dut.tp);

endmodule

// Example bind
bind register_ctrl_top register_ctrl_top_sva u_register_ctrl_top_sva(.dut);