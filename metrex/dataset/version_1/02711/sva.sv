// SVA for ConvolutionalEncoderAndViterbiDecoder
// Bind into the DUT; focuses on functional checks and essential coverage.

module ConvolutionalEncoderAndViterbiDecoder_sva #(parameter int n=4, m=8) ();

  // Access DUT scope via bind
  // Signals from DUT: in, clk, out, shift_reg, encoded_bits, state, next_state, decoded_bits

  // Basic setup
  default clocking cb @(posedge clk); endclocking
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Compile-time/structural guards
  initial begin
    if (n != 4) $error("SVA: parameter n must be 4 (design uses fixed taps)");
    if (m != 8) $error("SVA: parameter m must be 8 (design emits 8 encoded bits)");
  end

  // No X/Z on critical signals after the first clock
  assert property (!$isunknown({shift_reg, encoded_bits, state, next_state, decoded_bits, out})))
    else $error("SVA: X/Z detected on critical signals");

  // Encoder parity equations
  assert property (encoded_bits[0] == (shift_reg[0]^shift_reg[1]^shift_reg[2]^shift_reg[3]))
    else $error("SVA: encoded_bits[0] parity mismatch");
  assert property (encoded_bits[1] == (shift_reg[0]^shift_reg[1]^shift_reg[3]))
    else $error("SVA: encoded_bits[1] parity mismatch");
  assert property (encoded_bits[2] == (shift_reg[0]^shift_reg[2]^shift_reg[3]))
    else $error("SVA: encoded_bits[2] parity mismatch");
  assert property (encoded_bits[3] == (shift_reg[1]^shift_reg[2]^shift_reg[3]))
    else $error("SVA: encoded_bits[3] parity mismatch");
  assert property (encoded_bits[4] == (shift_reg[0]^shift_reg[1]^shift_reg[2]))
    else $error("SVA: encoded_bits[4] parity mismatch");
  assert property (encoded_bits[5] == (shift_reg[0]^shift_reg[2]))
    else $error("SVA: encoded_bits[5] parity mismatch");
  assert property (encoded_bits[6] == (shift_reg[1]^shift_reg[3]))
    else $error("SVA: encoded_bits[6] parity mismatch");
  assert property (encoded_bits[7] == (shift_reg[2]^shift_reg[3]))
    else $error("SVA: encoded_bits[7] parity mismatch");

  // Shift register update behavior per RTL (assignment truncation => equals previous 'in')
  assert property (shift_reg == $past(in))
    else $error("SVA: shift_reg must equal previous cycle 'in' (per current RTL)");

  // Decoder combinational mapping
  // For states 0..7: next_state = {state[2:0], encoded_bits[state[2:0]]}
  assert property ((state[3]==1'b0) |-> (next_state[3:1]==state[2:0] && next_state[0]==encoded_bits[state[2:0]]))
    else $error("SVA: next_state mapping mismatch for legal states 0..7");

  // For states 8..15: default hold
  assert property ((state[3]==1'b1) |-> (next_state == state))
    else $error("SVA: next_state must hold for illegal states 8..15");

  // Sequential pipeline checks
  assert property (state == $past(next_state))
    else $error("SVA: state must equal previous next_state");
  assert property (decoded_bits == $past(state))
    else $error("SVA: decoded_bits must equal previous state");
  assert property (out == decoded_bits)
    else $error("SVA: out must mirror decoded_bits");
  assert property (out == $past(state))
    else $error("SVA: out must equal state delayed by 1 cycle");

  // Coverage
  genvar i;
  generate
    for (i=0; i<8; i++) begin : COV_STATE_ENC
      cover property (state == i);
      cover property ($rose(encoded_bits[i]) or $fell(encoded_bits[i]));
    end
  endgenerate
  cover property ($rose(out) or $fell(out));
  cover property (state[3]==1'b1 && next_state==state); // default/hold path

endmodule

bind ConvolutionalEncoderAndViterbiDecoder
  ConvolutionalEncoderAndViterbiDecoder_sva #(.n(n), .m(m)) ();