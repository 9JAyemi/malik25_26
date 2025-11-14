// SVA for mux_2to1
module mux_2to1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic Y
);

  default clocking cb @($global_clock); endclocking

  // Core 4-state functional equivalence (includes X-merge semantics)
  assert property (
    Y === ((SEL === 1'b1) ? A :
           (SEL === 1'b0) ? B :
           ((A === B) ? A : 1'bx))
  ) else $error("mux_2to1: functional mismatch");

  // Deterministic select cases
  assert property ( (SEL === 1'b1) |-> (Y === A) ) else $error("mux_2to1: SEL=1 but Y!=A");
  assert property ( (SEL === 1'b0) |-> (Y === B) ) else $error("mux_2to1: SEL=0 but Y!=B");

  // X-propagation integrity
  assert property ( (!$isunknown({A,B,SEL})) |-> !$isunknown(Y) )
    else $error("mux_2to1: Y went X while inputs known");

  assert property ( (SEL !== 1'b0 && SEL !== 1'b1 && (A !== B)) |-> $isunknown(Y) )
    else $error("mux_2to1: expected X on Y when SEL is X/Z and A!=B");

  assert property ( (SEL !== 1'b0 && SEL !== 1'b1 && (A === B)) |-> (Y === A) )
    else $error("mux_2to1: expected Y==A when SEL is X/Z and A==B");

  // Sanity: Y only changes when some input changes
  assert property ( $changed(Y) |-> $changed({A,B,SEL}) )
    else $error("mux_2to1: Y changed without input change");

  // Coverage
  cover property ( (SEL===1'b1) && (Y===A) );
  cover property ( (SEL===1'b0) && (Y===B) );
  cover property ( $rose(SEL) && (A !== B) ##1 (Y !== $past(Y)) );
  cover property ( $fell(SEL) && (A !== B) ##1 (Y !== $past(Y)) );
  cover property ( (SEL !== 1'b0 && SEL !== 1'b1 && A !== B) && $isunknown(Y) );
  cover property ( (SEL !== 1'b0 && SEL !== 1'b1 && A === B) && (Y === A) );

endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (.A(A), .B(B), .SEL(SEL), .Y(Y));