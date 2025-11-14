// SVA for knight_rider
module knight_rider_sva #(
  parameter logic [9:0] LEDS_INIT = 10'b1100000000,
  parameter bit         DIR_INIT  = 1
)(
  input  logic        clk,
  input  logic [9:0]  leds,
  input  logic [3:0]  position,
  input  logic        direction,
  input  logic [7:0]  led_out
);

  default clocking cb @(posedge clk); endclocking

  // Past validity for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Time-0 init checks (no reset in DUT)
  initial begin
    assert (leds     === LEDS_INIT);
    assert (position === (DIR_INIT ? 4'd8 : 4'd0));
    assert (direction === DIR_INIT);
  end

  // Combinational mapping
  assert property (led_out == leds[8:1]);

  // No X/Z on key signals (sampled at clk)
  assert property (!$isunknown({leds, position, direction, led_out}));

  // Direction is MSB of position (position<8 => 0, else 1)
  assert property (direction == position[3]);

  // Position increments by 1 mod-16 each cycle
  assert property (disable iff (!past_valid)
                   position == $past(position) + 4'd1);

  // Shift behavior: leds updates per prior direction
  assert property (disable iff (!past_valid)
                   leds == ( $past(direction) ? ($past(leds) >> 1) : ($past(leds) << 1) ));

  // Direction changes iff position[3] changes
  assert property (disable iff (!past_valid)
                   $changed(direction) == $changed(position[3]));

  // Coverage: both directions, boundary flips, end LEDs seen, and periodicity
  cover property (direction==0);
  cover property (direction==1);
  cover property (position==4'd7  ##1 position==4'd8  && direction==1);
  cover property (position==4'd15 ##1 position==4'd0  && direction==0);
  cover property (led_out[7]); // top of window
  cover property (led_out[0]); // bottom of window
  cover property (1[*16] ##1 leds == $past(leds,16)); // 16-cycle return
endmodule

bind knight_rider knight_rider_sva #(
  .LEDS_INIT(LEDS_INIT),
  .DIR_INIT (DIR_INIT )
) i_knight_rider_sva (
  .clk      (clk),
  .leds     (leds),
  .position (position),
  .direction(direction),
  .led_out  (led_out)
);