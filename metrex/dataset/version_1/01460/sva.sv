// SVA for delay_module
module delay_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  in,
  input  logic [3:0]  out,
  input  logic [3:0]  delay_reg1,
  input  logic [3:0]  delay_reg2
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (synchronous clear)
  a_reset_clears: assert property (@(posedge clk) reset |-> (delay_reg1=='0 && delay_reg2=='0 && out=='0));

  // Stage behavior
  a_stage1_capture: assert property (delay_reg1 == in);
  a_stage2_pipeline: assert property ($past(1'b1) |-> delay_reg2 == $past(delay_reg1));
  a_out_pipeline:    assert property ($past(1'b1) |-> out       == $past(delay_reg2));

  // End-to-end 2-cycle latency when no reset in the window
  a_two_cycle_latency: assert property ( $past(!reset,1) && $past(!reset,2) |-> out == $past(in,2) );

  // No X/Z on state and output when active
  a_no_x_active: assert property ($past(1'b1) |-> !$isunknown({delay_reg1,delay_reg2,out}));

  // Coverage
  c_change_propagates: cover property ( $changed(in) ##2 (out == $past(in,2)) );
  c_reset_flush_then_data: cover property (@(posedge clk)
                               $fell(reset) ##1 (out=='0 && delay_reg2=='0) ##1 (out=='0));

endmodule

// Bind into DUT
bind delay_module delay_module_sva u_delay_module_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .delay_reg1(delay_reg1),
  .delay_reg2(delay_reg2)
);