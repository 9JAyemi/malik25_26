// SVA for up_down_counter
module up_down_counter_sva #(parameter int W=3)
(
  input logic              clk,
  input logic              reset,
  input logic              control,
  input logic [W-1:0]      count
);
  default clocking cb @(posedge clk); endclocking

  localparam logic [W-1:0] ZERO = '0;
  localparam logic [W-1:0] ONE  = {{W-1{1'b0}},1'b1};
  localparam logic [W-1:0] MAX  = {W{1'b1}};
  localparam logic [W-1:0] TWO  = ONE + ONE;

  // Reset behavior
  a_reset_hold:           assert property (reset |-> count == ZERO);
  a_reset_assert_effect:  assert property ($rose(reset) |=> count == ZERO);

  // Functional step (exclude cycles where previous sample was in reset)
  a_step_up:              assert property (disable iff (reset) ( control && !$past(reset)) |=> count == $past(count) + 1'b1);
  a_step_down:            assert property (disable iff (reset) (!control && !$past(reset)) |=> count == $past(count) - 1'b1);

  // First cycle after reset deassertion uses 0 as prior value
  a_after_release_step:   assert property ($fell(reset) |=> (control ? (count == ONE) : (count == MAX)));

  // Explicit wrap checks (redundant with step, but make intent clear)
  a_wrap_up:              assert property (disable iff (reset) (count == MAX  &&  control) |=> count == ZERO);
  a_wrap_down:            assert property (disable iff (reset) (count == ZERO && !control) |=> count == MAX);

  // No X/Z on key signals at clock edge
  a_no_x:                 assert property (!$isunknown({control, count}));

  // Coverage
  c_reset_pulse:          cover  property ($rose(reset) ##[1:$] $fell(reset));
  c_up_seq:               cover  property (disable iff (reset) (count == ZERO &&  control) |=> count == ONE |=> count == TWO);
  c_down_seq:             cover  property (disable iff (reset) (count == ZERO && !control) |=> count == MAX |=> count == (MAX - ONE));
  c_wrap_up:              cover  property (disable iff (reset) (count == MAX  &&  control) |=> count == ZERO);
  c_wrap_down:            cover  property (disable iff (reset) (count == ZERO && !control) |=> count == MAX);

endmodule

bind up_down_counter up_down_counter_sva #(.W(3)) u_up_down_counter_sva (
  .clk    (clk),
  .reset  (reset),
  .control(control),
  .count  (count)
);