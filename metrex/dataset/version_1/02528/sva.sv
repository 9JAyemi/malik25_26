// SVA for parity_checker
module parity_checker_sva (input [3:0] data, input parity);

  // Functional correctness (incl. X/Z propagation)
  ap_func:   assert property (parity === (^data));

  // Output known when input known
  ap_known:  assert property (!$isunknown(data) |-> !$isunknown(parity));

  // Stability across samples: if inputs don’t change, output doesn’t change
  ap_stable: assert property ($stable(data) |-> $stable(parity));

  // Dynamic parity behavior across samples (odd/even bit flips)
  ap_odd_flip_toggle:  assert property (($countones(data ^ $past(data,1,data)) % 2) == 1
                                        |-> (parity != $past(parity,1,parity)));
  ap_even_flip_hold:   assert property (($countones(data ^ $past(data,1,data)) % 2) == 0
                                        |-> (parity == $past(parity,1,parity)));

  // Coverage: both parity values observed
  cp_p0: cover property (parity == 1'b0);
  cp_p1: cover property (parity == 1'b1);

  // Coverage: each Hamming weight with correct parity
  cp_h0: cover property ($countones(data)==0 && parity==1'b0);
  cp_h1: cover property ($countones(data)==1 && parity==1'b1);
  cp_h2: cover property ($countones(data)==2 && parity==1'b0);
  cp_h3: cover property ($countones(data)==3 && parity==1'b1);
  cp_h4: cover property ($countones(data)==4 && parity==1'b0);

  // Coverage: single-bit flip toggles parity
  cp_single_flip: cover property ($countones(data ^ $past(data,1,data)) == 1
                                  && (parity != $past(parity,1,parity)));

endmodule

bind parity_checker parity_checker_sva sva (.data(data), .parity(parity));