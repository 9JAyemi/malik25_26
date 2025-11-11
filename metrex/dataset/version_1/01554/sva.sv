// SVA for module counter
// Bind this file to the DUT or instantiate counter_sva

module counter_sva (
  input logic       clk,
  input logic       rst,
  input logic       ctrl,
  input logic [3:0] out
);

  // Clocked checks (normal operation)
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // No X/Z on key signals during operation
  assert_no_x:        assert property (!$isunknown({ctrl,out}));

  // Step correctness (mod-16 up/down)
  assert_step_up:     assert property (ctrl  |-> out == (($past(out)==4'hF) ? 4'h0 : $past(out)+4'h1));
  assert_step_down:   assert property (!ctrl |-> out == (($past(out)==4'h0) ? 4'hF : $past(out)-4'h1));

  // The counter must change every cycle when not in reset
  assert_always_change: assert property (out != $past(out));

  // Asynchronous reset behavior
  assert_rst_async:   assert property (@(posedge rst) out == 4'h0);
  assert_rst_hold:    assert property (@(posedge clk)  rst |-> out == 4'h0);
  assert_rst_no_x:    assert property (@(posedge rst) !$isunknown(out));

  // Functional coverage
  // Reset seen
  cover_rst:          cover property (@(posedge rst) 1);

  // Increment without wrap
  cover_inc_nowrap:   cover property (ctrl && ($past(out)!=4'hF) && out==$past(out)+4'h1);

  // Decrement without wrap
  cover_dec_nowrap:   cover property (!ctrl && ($past(out)!=4'h0) && out==$past(out)-4'h1);

  // Wraps
  cover_inc_wrap:     cover property (ctrl && ($past(out)==4'hF) ##1 out==4'h0);
  cover_dec_wrap:     cover property (!ctrl && ($past(out)==4'h0) ##1 out==4'hF);

  // Back-to-back direction changes
  cover_inc_then_dec: cover property (ctrl ##1 !ctrl);
  cover_dec_then_inc: cover property (!ctrl ##1 ctrl);

  // 16-step cycles demonstrate full modulo behavior
  cover_full_inc_cycle: cover property (disable iff (rst) (out==4'h0 && ctrl) ##1 ctrl[*15] ##1 out==4'h0);
  cover_full_dec_cycle: cover property (disable iff (rst) (out==4'h0 && !ctrl) ##1 (!ctrl)[*15] ##1 out==4'h0);

endmodule

// Bind to DUT
bind counter counter_sva i_counter_sva (.clk(clk), .rst(rst), .ctrl(ctrl), .out(out));