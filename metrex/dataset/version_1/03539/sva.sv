// SVA for CLS_LED_Output_Multiplexer
// Bind into the DUT to check state machine, synchronizer, and LEDR mapping.

module CLS_LED_Output_Multiplexer_sva
(
  input  logic [9:0] PWM_CHANNEL_SIGS,
  input  logic       PWM_TIMER_TICK,
  input  logic       SRT_TICK,
  input  logic [9:0] LEDR,
  input  logic [4:0] frame_pos,
  input  logic [4:0] next_frame_pos,
  input  logic [4:0] frame_pos_sync
);

  // Track first tick seen per domain to safely use $past()
  logic srt_seen, pwm_seen;
  initial begin srt_seen = 1'b0; pwm_seen = 1'b0; end
  always @(posedge SRT_TICK)       srt_seen <= 1'b1;
  always @(posedge PWM_TIMER_TICK) pwm_seen <= 1'b1;

  // Valid state set
  function automatic logic is_valid_state (input logic [4:0] f);
    case (f)
      5'b00000, 5'b00001, 5'b00011, 5'b00010,
      5'b00110, 5'b00111, 5'b00101, 5'b00100,
      5'b01100, 5'b11100, 5'b10100, 5'b10101,
      5'b10111, 5'b10110, 5'b10010, 5'b10011,
      5'b10001, 5'b10000: is_valid_state = 1'b1;
      default:            is_valid_state = 1'b0;
    endcase
  endfunction

  // State transition mapping (comb)
  function automatic logic [4:0] map_next (input logic [4:0] f);
    case (f)
      5'b00000: map_next = 5'b00001;
      5'b00001: map_next = 5'b00011;
      5'b00011: map_next = 5'b00010;
      5'b00010: map_next = 5'b00110;
      5'b00110: map_next = 5'b00111;
      5'b00111: map_next = 5'b00101;
      5'b00101: map_next = 5'b00100;
      5'b00100: map_next = 5'b01100;
      5'b01100: map_next = 5'b11100;
      5'b11100: map_next = 5'b10100;
      5'b10100: map_next = 5'b10101;
      5'b10101: map_next = 5'b10111;
      5'b10111: map_next = 5'b10110;
      5'b10110: map_next = 5'b10010;
      5'b10010: map_next = 5'b10011;
      5'b10011: map_next = 5'b10001;
      5'b10001: map_next = 5'b10000;
      5'b10000: map_next = 5'b00000;
      default:  map_next = 5'b00000;
    endcase
  endfunction

  // Expected LEDR mapping from frame_pos_sync and pchs
  function automatic logic [9:0] expected_ledr (input logic [4:0] s, input logic [9:0] p);
    case (s)
      5'b00000: expected_ledr = { p[9], p[8], p[7], p[6], p[5], p[4], p[3], p[2], p[1], p[0] };
      5'b00001: expected_ledr = { p[8], p[9], p[6], p[5], p[4], p[3], p[2], p[1], p[0], p[0] };
      5'b00011: expected_ledr = { p[7], p[8], p[9], p[4], p[3], p[2], p[1], p[0], p[0], p[0] };
      5'b00010: expected_ledr = { p[6], p[7], p[8], p[9], p[2], p[1], p[0], p[0], p[0], p[0] };
      5'b00110: expected_ledr = { p[5], p[6], p[7], p[8], p[9], p[0], p[0], p[0], p[0], p[0] };
      5'b00111: expected_ledr = { p[4], p[5], p[6], p[7], p[8], p[9], p[0], p[0], p[0], p[0] };
      5'b00101: expected_ledr = { p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[0], p[0], p[0] };
      5'b00100: expected_ledr = { p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[0], p[0] };
      5'b01100: expected_ledr = { p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[0] };
      5'b11100: expected_ledr = { p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9] };
      5'b10100: expected_ledr = { p[0], p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[9], p[8] };
      5'b10101: expected_ledr = { p[0], p[0], p[0], p[1], p[2], p[3], p[4], p[9], p[8], p[7] };
      5'b10111: expected_ledr = { p[0], p[0], p[0], p[0], p[1], p[2], p[9], p[8], p[7], p[6] };
      5'b10110: expected_ledr = { p[0], p[0], p[0], p[0], p[0], p[9], p[8], p[7], p[6], p[5] };
      5'b10010: expected_ledr = { p[0], p[0], p[0], p[0], p[9], p[8], p[7], p[6], p[5], p[4] };
      5'b10011: expected_ledr = { p[0], p[0], p[0], p[9], p[8], p[7], p[6], p[5], p[4], p[3] };
      5'b10001: expected_ledr = { p[0], p[0], p[9], p[8], p[7], p[6], p[5], p[4], p[3], p[2] };
      5'b10000: expected_ledr = { p[0], p[9], p[8], p[7], p[6], p[5], p[4], p[3], p[2], p[1] };
      default:  expected_ledr = { p[0], p[9], p[8], p[7], p[5], p[4], p[3], p[2], p[1], p[0] };
    endcase
  endfunction

  // 1) next_frame_pos must be the combinational map of frame_pos
  assert property (@(posedge SRT_TICK or posedge PWM_TIMER_TICK)
                   next_frame_pos == map_next(frame_pos))
    else $error("next_frame_pos mapping mismatch");

  // 2) On each SRT_TICK, frame_pos takes the previously computed next_frame_pos
  assert property (@(posedge SRT_TICK) disable iff (!srt_seen)
                   frame_pos == $past(next_frame_pos, 1, SRT_TICK))
    else $error("frame_pos did not capture next_frame_pos on SRT_TICK");

  // 3) Legal encodings only for state flops
  assert property (@(posedge SRT_TICK or posedge PWM_TIMER_TICK)
                   is_valid_state(frame_pos))
    else $error("Illegal frame_pos encoding");
  assert property (@(posedge PWM_TIMER_TICK)
                   is_valid_state(frame_pos_sync))
    else $error("Illegal frame_pos_sync encoding");

  // 4) Synchronizer: PWM domain samples frame_pos correctly
  assert property (@(posedge PWM_TIMER_TICK) disable iff (!pwm_seen)
                   1'b1 |=> frame_pos_sync == $past(frame_pos, 1, PWM_TIMER_TICK))
    else $error("frame_pos_sync did not capture frame_pos on PWM_TIMER_TICK");

  // 5) LEDR mapping must match lookup from frame_pos_sync and PWM_CHANNEL_SIGS
  assert property (@(posedge SRT_TICK or posedge PWM_TIMER_TICK)
                   LEDR == expected_ledr(frame_pos_sync, PWM_CHANNEL_SIGS))
    else $error("LEDR mapping mismatch");

  // 6) No X/Z on key regs; if inputs are known, outputs should be known
  assert property (@(posedge SRT_TICK or posedge PWM_TIMER_TICK)
                   !$isunknown({frame_pos, next_frame_pos, frame_pos_sync}))
    else $error("Unknown (X/Z) detected on state regs");
  assert property (@(posedge PWM_TIMER_TICK)
                   !$isunknown(PWM_CHANNEL_SIGS) |-> !$isunknown(LEDR))
    else $error("LEDR has X/Z despite known inputs");

  // Coverage: hit each state in SRT domain
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00000);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00001);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00011);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00010);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00110);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00111);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00101);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b00100);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b01100);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b11100);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10100);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10101);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10111);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10110);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10010);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10011);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10001);
  cover property (@(posedge SRT_TICK) frame_pos == 5'b10000);

  // Coverage: full cycle order across SRT_TICKs
  cover property (@(posedge SRT_TICK)
      frame_pos==5'b00000 ##1
      frame_pos==5'b00001 ##1
      frame_pos==5'b00011 ##1
      frame_pos==5'b00010 ##1
      frame_pos==5'b00110 ##1
      frame_pos==5'b00111 ##1
      frame_pos==5'b00101 ##1
      frame_pos==5'b00100 ##1
      frame_pos==5'b01100 ##1
      frame_pos==5'b11100 ##1
      frame_pos==5'b10100 ##1
      frame_pos==5'b10101 ##1
      frame_pos==5'b10111 ##1
      frame_pos==5'b10110 ##1
      frame_pos==5'b10010 ##1
      frame_pos==5'b10011 ##1
      frame_pos==5'b10001 ##1
      frame_pos==5'b10000 ##1
      frame_pos==5'b00000);

  // Coverage: both tick domains active
  cover property (@(posedge SRT_TICK) 1);
  cover property (@(posedge PWM_TIMER_TICK) 1);

endmodule

bind CLS_LED_Output_Multiplexer CLS_LED_Output_Multiplexer_sva i_CLS_LED_Output_Multiplexer_sva
(
  .PWM_CHANNEL_SIGS(PWM_CHANNEL_SIGS),
  .PWM_TIMER_TICK(PWM_TIMER_TICK),
  .SRT_TICK(SRT_TICK),
  .LEDR(LEDR),
  .frame_pos(frame_pos),
  .next_frame_pos(next_frame_pos),
  .frame_pos_sync(frame_pos_sync)
);