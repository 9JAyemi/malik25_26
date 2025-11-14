// SVA for decoder_2to4
// Bind this checker to the DUT:
// bind decoder_2to4 decoder_2to4_sva sva(.in(in), .out(out));

module decoder_2to4_sva (
  input logic [1:0] in,
  input logic [3:0] out
);

  // Functional equivalence and one-hot when input is known
  property p_decode_equiv_onehot;
    !$isunknown(in) |-> (out == (4'b0001 << in)) and $onehot(out);
  endproperty
  a_decode_equiv_onehot: assert property (p_decode_equiv_onehot);

  // X-propagation: unknown input must yield unknown outputs
  a_x_prop: assert property ( $isunknown(in) |-> (out === 4'bxxxx) );

  // Stability: with stable input, output must be stable (no spurious glitches)
  a_stable: assert property ( $stable(in) |-> $stable(out) );

  // Functional coverage: all decode cases
  c_in00: cover property ( (in == 2'b00) and (out == 4'b0001) );
  c_in01: cover property ( (in == 2'b01) and (out == 4'b0010) );
  c_in10: cover property ( (in == 2'b10) and (out == 4'b0100) );
  c_in11: cover property ( (in == 2'b11) and (out == 4'b1000) );

  // Optional: observe unknown propagation in sims that exercise X/Z
  c_xflow: cover property ( $isunknown(in) and $isunknown(out) );

endmodule