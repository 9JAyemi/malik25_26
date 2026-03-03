// SVA for reg_32bits
module reg_32bits_sva(
  input logic         clk,
  input logic         rst,
  input logic         we,
  input logic [31:0]  d,
  input logic [31:0]  q,
  input logic [31:0]  q_reg
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears immediately and holds
  ap_async_reset_clears: assert property (@(posedge rst) ##0 (q == 32'h0));
  ap_reset_holds_zero:   assert property (rst |-> ##0 (q == 32'h0));

  // Write and hold behaviors
  ap_write_updates_q:    assert property ((!rst && we)   |-> ##0 (q == d));
  ap_hold_no_we:         assert property ((!rst && !we)  |-> ##0 (q == $past(q)));

  // No glitches: q only changes on clk or rst rising edges
  ap_q_changes_only_on_edges: assert property ( $changed(q) |-> ($rose(clk) || $rose(rst)) );

  // Output matches internal register after updates
  ap_q_eq_qreg_clk: assert property (@(posedge clk) ##0 (q == q_reg));
  ap_q_eq_qreg_rst: assert property (@(posedge rst) ##0 (q == q_reg));

  // Coverage
  cv_reset:                 cover property (@(posedge rst) ##0 (q == 32'h0));
  cv_write:                 cover property ((!rst && we)   ##0 (q == d));
  cv_hold:                  cover property ((!rst && !we)  ##0 (q == $past(q)));
  cv_back_to_back_writes:   cover property (@(posedge clk) !rst && we ##1 !rst && we && (d != $past(d)));
  cv_we_during_rst_ignored: cover property (@(posedge clk) rst && we ##0 (q == 32'h0));
endmodule

bind reg_32bits reg_32bits_sva sva_reg_32bits (.*);