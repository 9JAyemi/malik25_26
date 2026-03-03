// SVA checker for DemoInterconnect_jtag_axi_0_0_rd_status_flags_as__parameterized0_22

module demo_ic0_22_sva (
  input  logic        aclk,
  input  logic [1:0]  dest_out_bin_ff_reg,
  input  logic        out,
  input  logic        ram_empty_fb_i,
  input  logic        ram_empty_i
);

  default clocking cb @(posedge aclk); endclocking

  bit past1, past2;
  always_ff @(posedge aclk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // No Xs on key signals after first cycle
  assert property (past1 |-> !$isunknown(dest_out_bin_ff_reg[1]) && !$isunknown(ram_empty_fb_i)
                          && !$isunknown(ram_empty_i) && !$isunknown(out));

  // Pipeline correctness
  assert property (past1 |-> ram_empty_fb_i == $past(dest_out_bin_ff_reg[1]));
  assert property (past1 |-> ram_empty_i    == $past(ram_empty_fb_i));
  assert property (past2 |-> ram_empty_i    == $past(dest_out_bin_ff_reg[1],2));

  // Combinational out mirrors stage1, and end-to-end 1-cycle latency
  assert property (past1 |-> out == ram_empty_fb_i);
  assert property (past1 |-> out == $past(dest_out_bin_ff_reg[1]));

  // Input bit change implies next-cycle output change
  assert property (past1 && (dest_out_bin_ff_reg[1] != $past(dest_out_bin_ff_reg[1]))
                   |-> ##1 (out != $past(out)));

  // Coverage: rising/falling transfer 1-cycle later
  cover property (past1 && $rose(dest_out_bin_ff_reg[1]) ##1 $rose(out));
  cover property (past1 && $fell(dest_out_bin_ff_reg[1]) ##1 $fell(out));

endmodule

bind DemoInterconnect_jtag_axi_0_0_rd_status_flags_as__parameterized0_22 demo_ic0_22_sva sva_i (.*);