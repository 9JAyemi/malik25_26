// SVA for gray_code — concise, high-quality checks and coverage

bind gray_code gray_code_sva u_gray_code_sva(.clk(clk),
                                             .gray_out(gray_out),
                                             .binary_out(binary_out));

module gray_code_sva(
  input logic        clk,
  input logic [3:0]  gray_out,
  input logic [3:0]  binary_out
);
  default clocking cb @(posedge clk); endclocking

  // Track first sampled cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always @(cb) past_valid <= 1'b1;

  // Basic sanity: no X/Z on observed signals
  assert property (cb !$isunknown({gray_out, binary_out}));

  // Startup state as coded by initial block
  assert property (cb !past_valid |-> (binary_out==4'h0 && gray_out==4'h0));

  // Binary counter increments modulo-16
  assert property (cb disable iff(!past_valid)
                   binary_out == $past(binary_out) + 4'd1);

  // Gray output equals Gray(binary_out from previous cycle)
  assert property (cb disable iff(!past_valid)
                   gray_out == ($past(binary_out) ^ ($past(binary_out) >> 1)));

  // Equivalent relation using current sampled binary_out (one-cycle latency)
  assert property (cb disable iff(!past_valid)
                   gray_out == (((binary_out - 4'd1) ^ ((binary_out - 4'd1) >> 1))));

  // Successive Gray codes differ by exactly one bit
  assert property (cb disable iff(!past_valid)
                   $countones(gray_out ^ $past(gray_out)) == 1);

  // Coverage: observe full 16-step Gray cycle (all steps Hamming-1, period-16)
  cover property (cb past_valid ##1
                  ($countones(gray_out ^ $past(gray_out)) == 1)[*16]
                  and (gray_out == $past(gray_out,16)));

  // Coverage: explicit wrap of binary counter (F -> 0)
  cover property (cb disable iff(!past_valid)
                  ($past(binary_out)==4'hF && binary_out==4'h0));

endmodule