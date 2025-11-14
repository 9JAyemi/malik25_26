// SVA for dcf77_encoder
// Bind into DUT to check behavior concisely but thoroughly.
module dcf77_encoder_sva #(
  parameter CLOCK_FREQUENCY = 16000000,
  parameter CNT_MAX    = (11*CLOCK_FREQUENCY)/10,
  parameter CNT_SAMPLE = (15*CLOCK_FREQUENCY)/100
)(
  input  logic              clk,
  input  logic              reset,
  input  logic              dcf77_non_inverted,
  input  logic              dcf_sec,
  input  logic [58:0]       dcf_outputbits,
  input  logic [59:0]       dcf_bits,
  input  logic [30:0]       cnt,
  input  logic [2:0]        dcf_edge
);

  // Helpers
  wire rising  = (dcf_edge[2:1] == 2'b01);
  wire falling = (dcf_edge[2:1] == 2'b10);

  // No X/Z after reset released
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({dcf_sec, dcf_outputbits, dcf_bits, cnt, dcf_edge})
  );

  // Reset state holds on next clock after reset high
  assert property (@(posedge clk)
    reset |=> (dcf_outputbits == '0 && dcf_bits == '0 && dcf_sec == 1'b0 && cnt == 0 && dcf_edge == '0)
  );

  // Edge shift register tracks input
  assert property (@(posedge clk) disable iff (reset)
    dcf_edge == { $past(dcf_edge[1:0]), $past(dcf77_non_inverted) }
  );

  // Edge detection aligns with input transitions
  assert property (@(posedge clk) disable iff (reset)
    $rose(dcf77_non_inverted) |=> rising
  );
  assert property (@(posedge clk) disable iff (reset)
    $fell(dcf77_non_inverted) |=> falling
  );

  // Counter semantics: reset on rising, increment, and saturate
  assert property (@(posedge clk) disable iff (reset)
    $past(rising) |=> (cnt == 0)
  );
  assert property (@(posedge clk) disable iff (reset)
    $past(!rising && (cnt < CNT_MAX)) |=> (cnt == $past(cnt) + 1)
  );
  assert property (@(posedge clk) disable iff (reset)
    $past(!rising && (cnt >= CNT_MAX)) |=> (cnt == CNT_MAX)
  );

  // Bit capture on falling edge (0/1 by width threshold)
  assert property (@(posedge clk) disable iff (reset)
    $past(falling && (cnt < CNT_SAMPLE)) |-> (dcf_bits == {1'b0, $past(dcf_bits[59:1])})
  );
  assert property (@(posedge clk) disable iff (reset)
    $past(falling && (cnt >= CNT_SAMPLE)) |-> (dcf_bits == {1'b1, $past(dcf_bits[59:1])})
  );

  // Latch and minute marker: when rising with saturated count
  // Note: dcf_outputbits is 59b; assignment truncates MSB of dcf_bits (bit 59).
  assert property (@(posedge clk) disable iff (reset)
    $past(rising && (cnt == CNT_MAX)) |-> ($past(dcf_sec) &&
                                          (dcf_outputbits == $past(dcf_bits[58:0])) &&
                                          (dcf_bits == 60'b0))
  );

  // No spurious dcf_sec pulses
  assert property (@(posedge clk) disable iff (reset)
    $past(!(rising && (cnt == CNT_MAX))) |-> !$past(dcf_sec)
  );

  // dcf_sec is one-cycle pulse
  assert property (@(posedge clk) disable iff (reset)
    $past(dcf_sec) |-> !dcf_sec
  );

  // dcf_outputbits only updates on latch event
  assert property (@(posedge clk) disable iff (reset)
    $past(!(rising && (cnt == CNT_MAX))) |=> (dcf_outputbits == $past(dcf_outputbits))
  );

  // dcf_bits stability except on falling capture or latch-clear
  assert property (@(posedge clk) disable iff (reset)
    $past(!falling && !(rising && (cnt == CNT_MAX))) |-> (dcf_bits == $past(dcf_bits))
  );

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
    falling && (cnt < CNT_SAMPLE)
  );
  cover property (@(posedge clk) disable iff (reset)
    falling && (cnt >= CNT_SAMPLE)
  );
  cover property (@(posedge clk) disable iff (reset)
    rising && (cnt == CNT_MAX)
  );

endmodule

bind dcf77_encoder dcf77_encoder_sva #(
  .CLOCK_FREQUENCY(CLOCK_FREQUENCY),
  .CNT_MAX((11*CLOCK_FREQUENCY)/10),
  .CNT_SAMPLE((15*CLOCK_FREQUENCY)/100)
) u_dcf77_encoder_sva (.*);