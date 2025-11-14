// SystemVerilog Assertions for counter
// Bind these to the DUT; concise, high-quality checks and coverage.

module counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] count,
  input logic       control
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on key signals
  a_known:        assert property (!$isunknown({reset,count,control}));

  // Synchronous reset behavior
  a_reset_next:   assert property (reset |=> (count==4'h0 && control==1'b0));
  a_reset_hold:   assert property (reset && $past(reset) |-> (count==4'h0 && control==1'b0));

  // Counting rule: modulo-16 increment each cycle when not in reset
  a_count_mod16:  assert property (disable iff (reset)
                                   count == (($past(count)==4'hF) ? 4'h0 : ($past(count)+1)));

  // Control mirrors previous cycle's LSB of count
  a_ctrl_prev_lsb: assert property (disable iff (reset) control == $past(count[0]));

  // Key coverage
  c_wrap:         cover property (disable iff (reset) ($past(count)==4'hF && count==4'h0));

  c_full_cycle:   cover property (disable iff (reset)
                     (count==4'h0) ##1 (count==4'h1) ##1 (count==4'h2) ##1 (count==4'h3) ##1
                     (count==4'h4) ##1 (count==4'h5) ##1 (count==4'h6) ##1 (count==4'h7) ##1
                     (count==4'h8) ##1 (count==4'h9) ##1 (count==4'hA) ##1 (count==4'hB) ##1
                     (count==4'hC) ##1 (count==4'hD) ##1 (count==4'hE) ##1 (count==4'hF) ##1
                     (count==4'h0));

  c_ctrl_0:       cover property (disable iff (reset) control==1'b0);
  c_ctrl_1:       cover property (disable iff (reset) control==1'b1);

endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .count(count), .control(control));