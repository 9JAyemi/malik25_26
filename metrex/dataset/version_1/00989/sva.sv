// SVA for uart_rx
// Bind this checker into the DUT:
// bind uart_rx uart_rx_sva u_uart_rx_sva();

module uart_rx_sva;

  // Access DUT scope via bind
  // default clock and reset
  default clocking cb @ (posedge clk); endclocking
  default disable iff (rst);

  // Reset values
  ap_reset_vals: assert property (rst |=> (count==4'd0 && shift_reg==8'd0 &&
                                           start_bit==1'b0 && stop_bit==1'b1 &&
                                           data_out==8'd0 && parity==2'b00));

  // Counter behavior (intended)
  ap_cnt_reload: assert property (count==4'd0 |=> count==4'd11);
  ap_cnt_dec:    assert property ((count!=4'd0) |=> count == $past(count) - 1);

  // Updates at specific counts
  ap_start_cap:  assert property (count==4'd0  |=> start_bit == $past(rx));
  ap_shift_cap:  assert property (count==4'd1  |=> shift_reg == { $past(shift_reg[6:0]), $past(rx) });
  ap_stop_cap:   assert property (count==4'd10 |=> stop_bit  == $past(rx));
  ap_dout_cap:   assert property (count==4'd11 |=> data_out  == $past(shift_reg));

  // Only-change-when checks
  ap_only_start_changes_when_0: assert property ((start_bit  != $past(start_bit))  |-> $past(count)==4'd0);
  ap_only_shift_changes_when_1: assert property ((shift_reg  != $past(shift_reg))  |-> $past(count)==4'd1);
  ap_only_stop_changes_when_10: assert property ((stop_bit   != $past(stop_bit))   |-> $past(count)==4'd10);
  ap_only_dout_changes_when_11: assert property ((data_out   != $past(data_out))   |-> $past(count)==4'd11);

  // Parity combinational definition should match (flags conflicts with sequential write)
  ap_parity_func_00: assert property ((parity==2'b00) |-> parity_bit == 1'b1);
  ap_parity_func_01: assert property ((parity==2'b01) |-> parity_bit == ~shift_reg[0]);
  ap_parity_func_10: assert property ((parity==2'b10) |-> parity_bit == ~|shift_reg);
  ap_parity_func_11: assert property ((parity==2'b11) |-> parity_bit == ~(shift_reg[0]^|shift_reg[7:1]));

  // Parity should be clocked-only (exposes combinational self-update bug)
  ap_parity_clocked_only: assert property ($stable(parity));

  // Known-value checks
  ap_no_x_core: assert property (!$isunknown({count, shift_reg, start_bit, stop_bit, data_out}));

  // Coverage
  cp_start: cover property (count==4'd0  ##1 start_bit == $past(rx));
  cp_shift: cover property (count==4'd1  ##1 shift_reg == { $past(shift_reg[6:0]), $past(rx) });
  cp_stop:  cover property (count==4'd10 ##1 stop_bit  == $past(rx));
  cp_dout:  cover property (count==4'd11 ##1 data_out  == $past(shift_reg));

  // Observe a typical cycle hitting all key states within 16 clocks
  cp_key_counts_order: cover property (count==4'd0  ##[1:16] count==4'd1
                                       ##[1:16]     count==4'd10
                                       ##[1:16]     count==4'd11);

  // Exercise all parity modes
  cp_parity00: cover property (parity==2'b00);
  cp_parity01: cover property (parity==2'b01);
  cp_parity10: cover property (parity==2'b10);
  cp_parity11: cover property (parity==2'b11);

endmodule