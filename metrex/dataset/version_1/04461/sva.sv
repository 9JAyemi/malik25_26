// SVA for RFID_Receiver. Bind into DUT scope to access internals.
module RFID_Receiver_sva #(parameter int n = 8)
(
  input logic        clk,
  input logic        rst,
  input logic        rx,
  input logic [n-1:0] data_out,
  input logic        valid
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives known state next cycle
  a_reset_state: assert property (@(posedge clk) rst |=> count==0 && data_reg=='0 && start_reg==0 && valid==0);

  default disable iff (rst);

  // Counter behavior
  a_count_range: assert property (count < n);
  a_count_incr:  assert property (rx && count < n-1 |=> count == $past(count)+1);
  a_count_wrap:  assert property (rx && count == n-1 |=> count == 0);
  a_count_hold:  assert property (!rx |=> count == $past(count));

  // valid behavior
  a_valid_rise_on_wrap:    assert property ($rose(valid) |-> $past(rx) && $past(count)==n-1);
  a_valid_clears_on_rx0:   assert property (!rx |=> !valid);
  a_valid_sticky_while_rx: assert property ($past(valid) && rx |=> valid);

  // data_out update only on wrap, with correct value
  a_data_out_update_only_on_wrap: assert property ($changed(data_out) |-> $past(rx) && $past(count)==n-1);
  a_data_out_value_on_wrap:       assert property (rx && count==n-1 |=> data_out == $past(data_reg));

  // start_reg protocol
  a_start_set_on_wrap:  assert property (rx && count==n-1 |=> start_reg);
  a_start_clear_on_rx0: assert property ($past(start_reg) && !rx |=> !start_reg);

  // data_reg write model: set the indexed bit when rx==1 and not wrapping; otherwise stable
  a_data_reg_write_set_bit: assert property (rx && count < n-1
                                             |=> data_reg == ($past(data_reg) | ({{(n-1){1'b0}},1'b1} << $past(count))));
  a_data_reg_stable_when_no_write: assert property ((!rx) || (rx && count==n-1) |=> $stable(data_reg));

  // Coverage
  c_valid_pulse: cover property ($rose(valid));
  c_frame:       cover property (rx[*n] ##1 $rose(valid));
  c_clear:       cover property ($rose(valid) ##1 !rx ##1 !valid);
endmodule

bind RFID_Receiver RFID_Receiver_sva #(.n(n)) u_RFID_Receiver_sva (.*);