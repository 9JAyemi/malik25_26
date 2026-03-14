module triangular_waveform_sva (
  input logic clk,
  input logic reset,     // active-high synchronous reset
  input logic select,
  input logic [7:0] waveform
);

  // Track past validity to safely use $past()
  logic past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  ///// Reset behavior /////
  // During reset, waveform reflects selected counter reset value (0 for up, 255 for down).
  reset_waveform_matches_select: assert property (
    @(posedge clk) reset |-> (waveform == (select ? 8'hFF : 8'h00))
  );

  // On reset deassertion, first post-reset value steps to 1 (up) or 254 (down).
  after_reset_deassert_first_step: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && $fell(reset) |-> (waveform == (select ? 8'd254 : 8'd1))
  );

  ///// Select-stable step behavior /////
  // If select stays 0 for two cycles (no reset), output increments by 1 modulo 256.
  inc_when_select0_stable: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && ($past(select) == 1'b0) && (select == 1'b0)
      |-> (waveform == ({1'b0, $past(waveform)} + 9'd1)[7:0])
  );

  // If select stays 1 for two cycles (no reset), output decrements by 1 modulo 256.
  dec_when_select1_stable: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && ($past(select) == 1'b1) && (select == 1'b1)
      |-> (waveform == ({1'b0, $past(waveform)} + 9'd255)[7:0])
  );

  ///// Select toggle cross-relations /////
  // On 1->0 toggle (no reset), new value equals two's complement of previous (sum = 256).
  toggle_1to0_sum_256: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && $fell(select)
      |-> ( {1'b0, waveform} + {1'b0, $past(waveform)} ) == 9'h100
  );

  // On 0->1 toggle (no reset), new+previous equals 254.
  toggle_0to1_sum_254: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && $rose(select)
      |-> ( {1'b0, waveform} + {1'b0, $past(waveform)} ) == 9'h0FE
  );

  ///// Explicit wrap-around cases /////
  // Wrap on increment path: 0xFF -> 0x00 when select stays 0 (no reset).
  wrap_inc_ff_to_00: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && ($past(select) == 1'b0) && (select == 1'b0) && ($past(waveform) == 8'hFF)
      |-> (waveform == 8'h00)
  );

  // Wrap on decrement path: 0x00 -> 0xFF when select stays 1 (no reset).
  wrap_dec_00_to_ff: assert property (
    @(posedge clk) disable iff (reset)
      past_valid && !$past(reset) && ($past(select) == 1'b1) && (select == 1'b1) && ($past(waveform) == 8'h00)
      |-> (waveform == 8'hFF)
  );

endmodule