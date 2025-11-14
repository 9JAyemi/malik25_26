// SVA for led_controller
// Notes:
// - RX is 1-bit in the DUT but compared against 2..5 in the code. Assertions below
//   both check the actually reachable 1-bit behavior and, conditionally, the intended
//   multi-bit behavior when RX width >= 3.

bind led_controller led_controller_sva ();
module led_controller_sva;

  default clocking cb @(posedge CLK); endclocking

  // Helpers
  wire [4:0] leds = {LED1,LED2,LED3,LED4,LED5};
  logic past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // No X/Z after first cycle
  assert property (past_valid |-> !$isunknown({state, TX, leds}));

  // Actual hardware check: RX is 1-bit value
  assert property (RX inside {1'b0,1'b1});

  // From state 00:
  // - RX==1 -> next state 01 and all LEDs high
  assert property (state==2'b00 && RX==1'b1 |=> state==2'b01 && leds==5'b11111);

  // - RX==0 -> remain in 00, LEDs and TX hold
  assert property (state==2'b00 && RX==1'b0 |=> state==2'b00 && $stable(leds) && $stable(TX));

  // States 01 or 10: echo RX on TX and return to 00; LEDs stable
  assert property ((state inside {2'b01,2'b10}) |=> state==2'b00 && TX==$past(RX) && $stable(leds));

  // TX may change only if previous state was 01 or 10
  assert property ($changed(TX) |-> $past(state inside {2'b01,2'b10}));

  // LEDs may change only due to the state 00 decode (1-bit reachable: RX==1)
  generate
    if ($bits(RX) >= 3) begin : g_wide
      // Full decode checks when RX is at least 3 bits wide
      assert property (state==2'b00 && RX==3'd1 |=> state==2'b01 && leds==5'b11111);
      assert property (state==2'b00 && RX==3'd2 |=> state==2'b10 && leds==5'b00000);
      assert property (state==2'b00 && RX==3'd3 |=> state==2'b11 && leds==5'b11000);
      assert property (state==2'b00 && RX==3'd4 |=> state==2'b11 && leds==5'b00110);
      assert property (state==2'b00 && RX==3'd5 |=> state==2'b11 && leds==5'b00001);

      // Exit 11 on RX in {1,2,5}; in 11, LEDs/TX hold across that cycle
      assert property ($past(state==2'b11) |-> leds==$past(leds) && TX==$past(TX));
      assert property (state==2'b11 && (RX inside {3'd1,3'd2,3'd5}) |=> state==2'b00);

      // Origin checks
      assert property (state==2'b01 |-> $past(state==2'b00 && RX==3'd1));
      assert property (state==2'b10 |-> $past(state==2'b00 && RX==3'd2));
      assert property (state==2'b11 && !$past(state==2'b11) |-> $past(state==2'b00 && RX inside {3'd3,3'd4,3'd5}));

      // LED change cause (only legal on RX 1..5 in state 00)
      assert property ($changed(leds) |-> $past(state==2'b00 && RX inside {3'd1,3'd2,3'd3,3'd4,3'd5}));

      // Coverage (decode, echo, and 11 exits)
      cover property (state==2'b00 && RX==3'd1 ##1 state==2'b01 ##1 state==2'b00 && TX==$past(RX,1));
      cover property (state==2'b00 && RX==3'd2 ##1 state==2'b10 ##1 state==2'b00 && TX==$past(RX,1));
      cover property (state==2'b00 && RX==3'd3 ##1 state==2'b11);
      cover property (state==2'b00 && RX==3'd4 ##1 state==2'b11);
      cover property (state==2'b00 && RX==3'd5 ##1 state==2'b11);
      cover property (state==2'b11 && (RX inside {3'd1,3'd2,3'd5}) ##1 state==2'b00);
    end else begin : g_narrow
      // With 1-bit RX, states 10 and 11 are unreachable
      assert property (state!=2'b10 && state!=2'b11);

      // LED change cause (only from RX==1 in state 00)
      assert property ($changed(leds) |-> $past(state==2'b00 && RX==1'b1));

      // In state 11 (if ever reached due to bug), LEDs/TX should still hold across that cycle
      assert property ($past(state==2'b11) |-> leds==$past(leds) && TX==$past(TX));

      // Coverage for reachable flows
      cover property (state==2'b00 && RX==1'b1 ##1 state==2'b01 ##1 state==2'b00 && TX==$past(RX,1));
      cover property (state==2'b00 && RX==1'b0 ##1 state==2'b00);
    end
  endgenerate

endmodule