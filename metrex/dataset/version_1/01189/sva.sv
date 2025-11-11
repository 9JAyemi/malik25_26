// SVA checker for audio_codec
module audio_codec_sva;
  // Bound into audio_codec scope; can reference DUT signals/params directly
  default clocking cb @(posedge clk); endclocking

  // Parameter/width sanity (DUT hard-codes 16-bit zeros)
  initial begin
    assert (m == 16)
      else $error("audio_codec: m (%0d) must be 16 due to {16{1'b0}} literal", m);
    assert (fs > 0);
    assert (bitrate > 0);
    assert (mode == "MP3");
  end

  // Past-valid guard for $past
  bit past_valid; initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Knownness checks
  assert property (!$isunknown(ctrl_in));
  assert property (!$isunknown(ctrl_out));
  assert property (!$isunknown(out));

  // ctrl_out mirrors ctrl_in with 1-cycle latency (NBA semantics)
  assert property (past_valid |-> ctrl_out == $past(ctrl_in));

  // ctrl_out changes only if ctrl_in changed in prior cycle; stable follows stable
  assert property (past_valid && $changed(ctrl_out) |-> $past($changed(ctrl_in)));
  assert property (past_valid && $stable(ctrl_in)  |-> $stable(ctrl_out));

  // out is always zero (m-bit)
  assert property (out == '0);

  // Basic functional coverage
  cover property (past_valid && ctrl_in==0 ##1 ctrl_out==0 && out=='0);
  cover property (past_valid && ctrl_in==1 ##1 ctrl_out==1 && out=='0);
  cover property (ctrl_in==0 ##1 ctrl_in==1); // 0->1
  cover property (ctrl_in==1 ##1 ctrl_in==0); // 1->0
  cover property (ctrl_in==0[*3]);
  cover property (ctrl_in==1[*3]);
  cover property ($changed(in)); // stimulate data path (though unused)
endmodule

// Bind the checker into all instances of audio_codec
bind audio_codec audio_codec_sva sva();