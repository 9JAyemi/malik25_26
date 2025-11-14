// SVA for parity_generator: concise, high-quality checks and coverage
module parity_generator_sva (input logic [7:0] in, input logic parity);

  // Drive properties on any edge of any input bit; add ##0 to avoid delta races
  // Event expression expanded explicitly for portability
  property any_in_edge; 
    @(posedge in[0] or negedge in[0] or
      posedge in[1] or negedge in[1] or
      posedge in[2] or negedge in[2] or
      posedge in[3] or negedge in[3] or
      posedge in[4] or negedge in[4] or
      posedge in[5] or negedge in[5] or
      posedge in[6] or negedge in[6] or
      posedge in[7] or negedge in[7]) 1;
  endproperty

  // Functional equivalence (4-state) at all input changes
  property p_equiv;
    any_in_edge ##0 (parity === (^in));
  endproperty
  assert property (p_equiv)
    else $error("parity != ^in: parity=%0b ^in=%0b in=%0h", parity, ^in, in);

  // If inputs are all known, parity must be known
  property p_known_out_when_known_in;
    any_in_edge ##0 (!$isunknown(in)) |-> (!$isunknown(parity));
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("parity X/Z with fully-known input: in=%0h parity=%b", in, parity);

  // Parity delta equals parity of input delta (robust transition check)
  property p_delta;
    any_in_edge disable iff ($isunknown($past(in)) || $isunknown($past(parity)))
      ##0 ((parity ^ $past(parity)) === ^(in ^ $past(in)));
  endproperty
  assert property (p_delta)
    else $error("delta mismatch: prev(in,par)=%0h,%0b curr(in,par)=%0h,%0b",
                $past(in), $past(parity), in, parity);

  // Coverage: both parity values observed
  cover property (any_in_edge ##0 (parity == 1'b0));
  cover property (any_in_edge ##0 (parity == 1'b1));

  // Coverage: odd/even number of input bit flips vs parity toggle/hold
  cover property (any_in_edge ##0 (^(in ^ $past(in))) && (parity ^ $past(parity)));
  cover property (any_in_edge ##0 !(^(in ^ $past(in))) && !(parity ^ $past(parity)));

endmodule

bind parity_generator parity_generator_sva i_parity_generator_sva (.in(in), .parity(parity));