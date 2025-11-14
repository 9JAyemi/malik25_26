// SVA for mux4to1. Bind into the DUT; uses clockless concurrent assertions.

module mux4to1_sva;

  // Functional correctness per select value
  property p_sel_A; (S1===1'b0 && S0===1'b0) |-> (Y === A); endproperty
  property p_sel_B; (S1===1'b0 && S0===1'b1) |-> (Y === B); endproperty
  property p_sel_C; (S1===1'b1 && S0===1'b0) |-> (Y === C); endproperty
  property p_sel_D; (S1===1'b1 && S0===1'b1) |-> (Y === D); endproperty
  assert property (p_sel_A);
  assert property (p_sel_B);
  assert property (p_sel_C);
  assert property (p_sel_D);

  // Internal wiring checks
  assert property (not_s0 === ~S0);
  assert property (not_s1 === ~S1);
  assert property (Y === Y_int);

  // Select-term one-hot when selects are known
  assert property ( (S0 inside {0,1}) && (S1 inside {0,1}) |->
                    ((~S1 & ~S0) ^ (~S1 & S0) ^ (S1 & ~S0) ^ (S1 & S0)) );

  // Coverage: all select combinations
  cover property (S1===1'b0 && S0===1'b0);
  cover property (S1===1'b0 && S0===1'b1);
  cover property (S1===1'b1 && S0===1'b0);
  cover property (S1===1'b1 && S0===1'b1);

  // Coverage: each data path propagates 0 and 1 when selected
  cover property (S1===0 && S0===0 && A===0 && Y===0);
  cover property (S1===0 && S0===0 && A===1 && Y===1);
  cover property (S1===0 && S0===1 && B===0 && Y===0);
  cover property (S1===0 && S0===1 && B===1 && Y===1);
  cover property (S1===1 && S0===0 && C===0 && Y===0);
  cover property (S1===1 && S0===0 && C===1 && Y===1);
  cover property (S1===1 && S0===1 && D===0 && Y===0);
  cover property (S1===1 && S0===1 && D===1 && Y===1);

endmodule

bind mux4to1 mux4to1_sva m_mux4to1_sva();