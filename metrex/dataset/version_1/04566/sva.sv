// SVA checker for EtherCAT_slave
module EtherCAT_slave_sva #(parameter int n = 8)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [n-1:0]      in_receive,
  input  logic [n-1:0]      out_send
);

  // Async reset drives zero immediately (delta cycle)
  a_async_reset_zero: assert property (@(posedge rst) ##0 (out_send == '0));

  // While reset held, output stays zero on every clock
  a_hold_zero_in_reset: assert property (@(posedge clk) rst |-> (out_send == '0));

  // Pass-through: when not in reset, next-cycle out equals current in
  a_pass_through: assert property (@(posedge clk) !rst |-> ##1 (out_send == $past(in_receive)));

  // No X/Z on output
  a_no_xz_out: assert property (@(posedge clk) !$isunknown(out_send));

  // After reset assertion, next clock still zero (no glitch on first clk)
  a_zero_next_clk_after_rst: assert property (@(posedge clk) $rose(rst) |=> (out_send == '0));

  // Coverage
  c_reset_assert:   cover property (@(posedge clk) $rose(rst));
  c_reset_deassert: cover property (@(posedge clk) $fell(rst));

  // Cover pass-through on any data change
  c_pass_through_any: cover property (@(posedge clk)
                                      !rst && (in_receive != $past(in_receive)) ##1
                                      (out_send != $past(out_send)));

  // Cover pass-through for all-zeros and all-ones
  c_pass_zero: cover property (@(posedge clk) !rst && (in_receive == '0) ##1 (out_send == '0));
  c_pass_ones: cover property (@(posedge clk) !rst && (in_receive == {n{1'b1}}) ##1 (out_send == {n{1'b1}}));

endmodule

// Bind into DUT
bind EtherCAT_slave EtherCAT_slave_sva #(.n(n)) ethercat_slave_sva_i
(
  .clk(clk),
  .rst(rst),
  .in_receive(in_receive),
  .out_send(out_send)
);