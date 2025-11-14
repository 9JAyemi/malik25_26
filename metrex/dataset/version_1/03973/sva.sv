// SVA checker for mux_2_1
module mux_2_1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic Y
);

  // Helper event: trigger on any input edge; use ##0 to avoid preponed-region race
  // Functional correctness: when inputs are known, Y must equal selected input
  property p_mux_func;
    @(posedge A or negedge A or posedge B or negedge B or posedge SEL or negedge SEL)
      !$isunknown({A,B,SEL}) |-> ##0 (Y === (SEL ? B : A));
  endproperty
  assert property (p_mux_func) else $error("mux_2_1: Y != (SEL ? B : A)");

  // No X/Z propagation when inputs are known
  property p_y_known_when_inputs_known;
    @(posedge A or negedge A or posedge B or negedge B or posedge SEL or negedge SEL)
      !$isunknown({A,B,SEL}) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_y_known_when_inputs_known) else $error("mux_2_1: Y is X/Z while inputs are known");

  // Directed covers: both legs exercised and data-driven updates observed
  cover property (@(negedge SEL) ##0 (Y === A) && !$isunknown(A));
  cover property (@(posedge SEL) ##0 (Y === B) && !$isunknown(B));
  cover property (@(posedge A or negedge A) (!SEL && !$isunknown({A,SEL})) ##0 (Y === A));
  cover property (@(posedge B or negedge B) ( SEL && !$isunknown({B,SEL})) ##0 (Y === B));

  // Observe both output transitions
  cover property (@(posedge Y));
  cover property (@(negedge Y));

endmodule

// Bind into the DUT
bind mux_2_1 mux_2_1_sva u_mux_2_1_sva (.A(A), .B(B), .SEL(SEL), .Y(Y));