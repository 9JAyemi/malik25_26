// SVA for BLOCK1A
module BLOCK1A_sva (input PIN2, GIN1, GIN2, PHI, GOUT);

  default clocking cb @(posedge PHI); endclocking

  // Functional correctness (registered, 1-cycle latency)
  property p_func;
    $past(1'b1) && !$isunknown($past({PIN2,GIN1,GIN2})) |->
      GOUT == ~( $past(GIN2) & ($past(PIN2) | $past(GIN1)) );
  endproperty
  assert property (p_func);

  // No X on sampled inputs/outputs at clock edge
  assert property (@cb !$isunknown({PIN2,GIN1,GIN2}));
  assert property (@cb !$isunknown(GOUT));

  // Basic functional covers
  cover property (@cb GOUT == 1'b0);
  cover property (@cb GOUT == 1'b1);
  cover property (@cb $rose(GOUT));
  cover property (@cb $fell(GOUT));

  // Exercise all input combinations at the sampling edge
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b000);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b001);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b010);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b011);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b100);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b101);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b110);
  cover property (@cb {PIN2,GIN1,GIN2} == 3'b111);

endmodule

// Bind into DUT
bind BLOCK1A BLOCK1A_sva u_BLOCK1A_sva (.*);