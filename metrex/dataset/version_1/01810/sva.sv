// SVA for decoder. Bind to the DUT to access internals.
module decoder_sva (decoder d);

  // Use enable's posedge as the clock; build a 2-cycle warmup for $past.
  default clocking cb @(posedge d.enable); endclocking

  logic [1:0] warmup;
  initial warmup = 2'b00;
  always @(posedge d.enable) warmup <= {warmup[0], 1'b1};

  // Stage-1: capture
  assert property (d.stage1_out == d.in);

  // Stage-2: decode previous stage1_out
  assert property (disable iff (!warmup[0])
                   d.stage2_out == (4'b0001 << $past(d.stage1_out)));

  // Blocking hazard check: out is previous stage2_out
  assert property (disable iff (!warmup[0])
                   d.out == $past(d.stage2_out));

  // End-to-end: 2-cycle latency from in to out
  assert property (disable iff (!warmup[1])
                   d.out == (4'b0001 << $past(d.in,2)));

  // One-hot encodings (and non-zero) after pipeline fills
  assert property (disable iff (!warmup[0]) $onehot(d.stage2_out));
  assert property (disable iff (!warmup[1]) $onehot(d.out));

  // No X/Z on outputs once valid
  assert property (disable iff (!warmup[0]) !$isunknown(d.stage2_out));
  assert property (disable iff (!warmup[1]) !$isunknown(d.out));

  // Functional coverage: hit all input codes and corresponding outputs 2 cycles later
  genvar i;
  for (i = 0; i < 4; i++) begin : cov_decode
    cover property ( (d.in == i[1:0]) ##2 (d.out == (4'b0001 << i)) );
  end

  // Coverage: pipeline warmed up
  cover property (warmup[1]);

endmodule

// Example bind (uncomment in your testbench or a separate bind file):
// bind decoder decoder_sva sva_inst();