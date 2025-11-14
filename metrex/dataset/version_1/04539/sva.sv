// SVA for reverse_parity — bindable, concise, and focused on functional/CDC/X checks + coverage

module reverse_parity_sva (
  input  logic [2:0] in_vec,
  input  logic [2:0] out_vec,
  input  logic       even_parity
);
  // Sample on any input change
  default clocking cb @(in_vec); endclocking

  // Functional mapping (allow delta-cycle settle)
  assert property ( !$isunknown(in_vec) |-> ##0 (out_vec == {in_vec[2], in_vec[1], in_vec[0]}) );
  assert property ( !$isunknown(in_vec) |-> ##0 (even_parity == (in_vec[0] ^ in_vec[1] ^ in_vec[2])) );

  // No X on outputs when inputs are known
  assert property ( !$isunknown(in_vec) |-> ##0 (!($isunknown(out_vec) || $isunknown(even_parity))) );

  // Outputs only change in response to an input change
  assert property (@(out_vec)      $changed(in_vec));
  assert property (@(even_parity)  $changed(in_vec));

  // Parity toggles iff Hamming distance between successive inputs is odd
  assert property (
    (!$isunknown(in_vec) && !$isunknown($past(in_vec)))
    |-> ((($countones(in_vec ^ $past(in_vec)) % 2) != 0) ? $changed(even_parity) : !$changed(even_parity))
  );

  // Coverage: all input codes observed
  cover property ( in_vec == 3'b000 );
  cover property ( in_vec == 3'b001 );
  cover property ( in_vec == 3'b010 );
  cover property ( in_vec == 3'b011 );
  cover property ( in_vec == 3'b100 );
  cover property ( in_vec == 3'b101 );
  cover property ( in_vec == 3'b110 );
  cover property ( in_vec == 3'b111 );

  // Coverage: parity behavior across single/two/three-bit flips
  cover property ( !$isunknown($past(in_vec)) && $onehot(in_vec ^ $past(in_vec))                     && $changed(even_parity) );
  cover property ( !$isunknown($past(in_vec)) && ($countones(in_vec ^ $past(in_vec)) == 2)           && !$changed(even_parity) );
  cover property ( !$isunknown($past(in_vec)) && ($countones(in_vec ^ $past(in_vec)) == 3)           && $changed(even_parity) );

endmodule

bind reverse_parity reverse_parity_sva rp_sva (
  .in_vec(in_vec),
  .out_vec(out_vec),
  .even_parity(even_parity)
);