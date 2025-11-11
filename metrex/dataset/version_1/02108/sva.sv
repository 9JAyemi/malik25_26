// SVA for PhaseDelayMain
// Concise, high-quality checks and coverage

module PhaseDelayMain_sva
  #(parameter int NUM_SIZE=7,
    parameter int SEQ_SIZE=NUM_SIZE+4)
  (input logic clk, input logic decoderInput, input logic sigOut);

  // This bind module is elaborated inside PhaseDelayMain; it can see seq1..seq4.
  // Sanity on params
  initial begin
    assert (NUM_SIZE+1 < SEQ_SIZE)
      else $fatal(1,"NUM_SIZE+1 must be < SEQ_SIZE");
  end

  // Make $past usable
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Rotate-right-by-1 on each sequence
  assert property (@(posedge clk) past_valid |-> seq1 == {$past(seq1[0]), $past(seq1[SEQ_SIZE-1:1])});
  assert property (@(posedge clk) past_valid |-> seq2 == {$past(seq2[0]), $past(seq2[SEQ_SIZE-1:1])});
  assert property (@(posedge clk) past_valid |-> seq3 == {$past(seq3[0]), $past(seq3[SEQ_SIZE-1:1])});
  assert property (@(posedge clk) past_valid |-> seq4 == {$past(seq4[0]), $past(seq4[SEQ_SIZE-1:1])});

  // Decode mapping: sigOut is a pure function of seq1 window and decoderInput
  let abc_p = $past({seq1[NUM_SIZE-1], seq1[NUM_SIZE], seq1[NUM_SIZE+1]});
  let din_p = $past(decoderInput);
  assert property (@(posedge clk) past_valid |-> 
    $past(sigOut) ==
      (abc_p == 3'b101 ? $past(seq2[NUM_SIZE + din_p]) :
       abc_p == 3'b110 ? $past(seq3[NUM_SIZE + din_p]) :
       abc_p == 3'b111 ? $past(seq4[NUM_SIZE + din_p]) :
       1'b0));

  // No X/Z after init on key state and output
  assert property (@(posedge clk) past_valid |-> !$isunknown({sigOut, seq1, seq2, seq3, seq4}));

  // Check initial sequence contents (only when SEQ_SIZE matches DUT's literals)
  generate
    if (SEQ_SIZE == 11) begin : g_init_chk
      // First active clock
      assert property (@(posedge clk) !past_valid ##1 past_valid |->
        (seq1 == 11'b01000000000 &&
         seq2 == 11'b01001000000 &&
         seq3 == 11'b01010000000 &&
         seq4 == 11'b01011000000));
    end
  endgenerate

  // Functional coverage: hit all 16 case entries at least once
  // (Covers the exact 4'b{seq1[NUM_SIZE-1:NUM_SIZE+1], decoderInput} table)
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0000);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0001);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0010);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0011);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0100);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0101);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0110);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b0111);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1000);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1001);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1010);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1011);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1100);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1101);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1110);
  cover property (@(posedge clk) {seq1[NUM_SIZE-1],seq1[NUM_SIZE],seq1[NUM_SIZE+1],decoderInput} == 4'b1111);

endmodule

// Bind into DUT
bind PhaseDelayMain PhaseDelayMain_sva #(.NUM_SIZE(NUM_SIZE), .SEQ_SIZE(SEQ_SIZE))
  PhaseDelayMain_sva_i (.clk(clk), .decoderInput(decoderInput), .sigOut(sigOut));