// SVA for audio_codec
// Bind into DUT to check/reset, pass-through, muxing, stability, and basic coverage

module audio_codec_sva #(parameter string format = "MP3") (
  input  logic         clk,
  input  logic         rst,
  input  logic [15:0]  audio_in,
  input  logic [7:0]   config_data,
  input  logic         config_en,
  input  logic [15:0]  audio_out,
  input  logic         valid_out,
  // internal regs
  input  logic [15:0]  audio_compressed,
  input  logic [15:0]  audio_decompressed
);

  default clocking cb @(posedge clk); endclocking

  // Reset drives all internal/outputs to 0 in the next cycle
  assert property (@cb rst |=> (audio_compressed==16'h0 && audio_decompressed==16'h0 &&
                                valid_out==1'b0 && audio_out==16'h0));

  // No X/Z on key outputs in normal operation
  assert property (@cb disable iff (rst)
                   !$isunknown({audio_out, valid_out, audio_compressed, audio_decompressed}));

  // Output mux must reflect format selection every cycle
  assert property (@cb disable iff (rst)
                   audio_out == ((format=="MP3") ? audio_compressed : audio_decompressed));

  // When not configuring, pass-through update in one cycle and valid asserted
  assert property (@cb disable iff (rst)
                   !config_en |=> (audio_compressed==$past(audio_in) &&
                                   audio_decompressed==$past(audio_in) &&
                                   audio_out==$past(audio_in) &&
                                   valid_out==1'b1));

  // While configuring, hold state (no updates)
  assert property (@cb disable iff (rst)
                   config_en |=> $stable({audio_compressed, audio_decompressed, audio_out, valid_out}));

  // Optional: once valid becomes 1, it never drops while out of reset
  assert property (@cb disable iff (rst)
                   valid_out |=> valid_out);

  // Coverage

  // See data path produce a valid sample
  cover property (@cb !rst && !config_en ##1 (valid_out && audio_out==$past(audio_in)));

  // See audio_in change propagate to audio_out next cycle
  cover property (@cb !rst && !config_en && $changed(audio_in) ##1 (audio_out==$past(audio_in)));

  // Exercise config phases
  cover property (@cb $rose(config_en));
  cover property (@cb $fell(config_en));

  // Reset then produce a valid output
  cover property (@cb rst ##1 !rst ##1 valid_out);

endmodule

// Bind into the DUT
bind audio_codec audio_codec_sva #(.format(format)) audio_codec_sva_i (
  .clk(clk),
  .rst(rst),
  .audio_in(audio_in),
  .config_data(config_data),
  .config_en(config_en),
  .audio_out(audio_out),
  .valid_out(valid_out),
  .audio_compressed(audio_compressed),
  .audio_decompressed(audio_decompressed)
);