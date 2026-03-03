// SVA checker for BLOCK1
// Focused, concise, high-quality assertions and coverage

`ifndef SYNTHESIS
module BLOCK1_sva (
  input logic PIN1, PIN2, GIN1, GIN2, PHI,
  input logic POUT, GOUT
);
  default clocking cb @(posedge PHI); endclocking

  // Functional correctness (only when relevant inputs are known)
  a_pout_func: assert property ( !$isunknown({PIN1,PIN2})
                                 |-> (POUT == ~(PIN1 | PIN2)) );

  a_gout_func: assert property ( !$isunknown({GIN2,PIN2,GIN1})
                                 |-> (GOUT == ~(GIN2 & (PIN2 | GIN1))) );

  // If inputs are all known, outputs must be known
  a_known_out_when_known_in: assert property (
    !$isunknown({PIN1,PIN2,GIN1,GIN2}) |-> !$isunknown({POUT,GOUT})
  );

  // PHI must not influence outputs (when inputs are held stable)
  a_no_phi_dependence: assert property (
    $stable({PIN1,PIN2,GIN1,GIN2}) |-> $stable({POUT,GOUT})
  );

  // Minimal functional coverage
  // POUT input space (PIN1,PIN2)
  cover property ( {PIN1,PIN2} == 2'b00 );
  cover property ( {PIN1,PIN2} == 2'b01 );
  cover property ( {PIN1,PIN2} == 2'b10 );
  cover property ( {PIN1,PIN2} == 2'b11 );

  // GOUT input space (GIN2,PIN2,GIN1)
  cover property ( {GIN2,PIN2,GIN1} == 3'b000 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b001 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b010 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b011 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b100 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b101 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b110 );
  cover property ( {GIN2,PIN2,GIN1} == 3'b111 );

  // Output toggle coverage
  cover property ( $rose(POUT) );  cover property ( $fell(POUT) );
  cover property ( $rose(GOUT) );  cover property ( $fell(GOUT) );

endmodule

// Bind into all instances of BLOCK1
bind BLOCK1 BLOCK1_sva i_BLOCK1_sva (.*);
`endif