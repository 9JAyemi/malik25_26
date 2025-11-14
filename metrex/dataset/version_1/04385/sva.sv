// SVA for concat_8bit
module concat_8bit_sva (
  input clk,
  input reset,
  input [7:0] a,
  input [7:0] b,
  input ctrl,
  input [15:0] out,
  input [15:0] temp
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives/holds zero
  a_async_reset_now_zero: assert property (@(posedge reset) (temp==16'h0 && out==16'h0));
  a_reset_holds_zero:     assert property (@(posedge clk)   reset |-> (temp==16'h0 && out==16'h0));

  // Out is always tied to temp
  a_out_equals_temp:      assert property (out == temp);

  // Functional behavior: next-cycle out/temp reflect previous sampled inputs (when previous cycle not in reset)
  a_concat_function: assert property (
    (!reset && !$past(reset)) |->
      ( temp == ( $past(ctrl) ? {$past(a),$past(b)} : {$past(b),$past(a)} ) &&
        out  == ( $past(ctrl) ? {$past(a),$past(b)} : {$past(b),$past(a)} ) )
  );

  // Basic X-checks in normal operation
  a_ctrl_known:  assert property (disable iff (reset) !$isunknown(ctrl));
  a_out_known:   assert property (disable iff (reset) !$isunknown(out));
  a_in_known:    assert property (disable iff (reset) !$isunknown({a,b}));

  // Coverage
  c_reset_seen:   cover property (@(posedge clk) reset);
  c_ctrl1_path:   cover property (disable iff (reset) ctrl ##1 (out == {$past(a),$past(b)}));
  c_ctrl0_path:   cover property (disable iff (reset) !ctrl ##1 (out == {$past(b),$past(a)}));
  c_ctrl_toggle:  cover property (disable iff (reset) ctrl ##1 !ctrl);

endmodule

// Bind into DUT
bind concat_8bit concat_8bit_sva u_concat_8bit_sva (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .ctrl(ctrl),
  .out(out),
  .temp(temp)
);