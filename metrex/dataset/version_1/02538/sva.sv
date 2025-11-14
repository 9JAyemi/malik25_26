// SVA for counter_4bit
// Bind this file to the DUT or instantiate alongside.

module counter_4bit_sva (
  input logic clk,
  input logic rst,
  input logic [3:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset: if rst is 1 on a clock, out is 0 on next clock.
  a_reset_next_is_zero: assert property (rst |=> out == 4'd0);

  // Functional next-state when not in reset: increment, with wrap at 15.
  a_next_state: assert property (
    !$past(rst) |-> out == (($past(out) == 4'd15) ? 4'd0 : $past(out) + 4'd1)
  );

  // Optional robustness: after any reset cycle, out is known and zero.
  a_no_x_after_reset: assert property ($past(rst) |-> (out == 4'd0 && !$isunknown(out)));

  // Coverage
  c_reset_effect: cover property (rst ##1 out == 4'd0);
  c_wrap:         cover property (!$past(rst) && $past(out) == 4'd15 && out == 4'd0);

  // Full 0..15..0 count sequence without reset
  c_full_count: cover property (
    disable iff (rst)
      out==4'd0 ##1 out==4'd1 ##1 out==4'd2 ##1 out==4'd3 ##1
      out==4'd4 ##1 out==4'd5 ##1 out==4'd6 ##1 out==4'd7 ##1
      out==4'd8 ##1 out==4'd9 ##1 out==4'd10 ##1 out==4'd11 ##1
      out==4'd12 ##1 out==4'd13 ##1 out==4'd14 ##1 out==4'd15 ##1 out==4'd0
  );
endmodule

// Bind into DUT
bind counter_4bit counter_4bit_sva sva_i (.clk(clk), .rst(rst), .out(out));