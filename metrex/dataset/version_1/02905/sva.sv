// SVA for karnaugh_map: F must implement odd parity (A^B^C) for known inputs,
// and drive 0 when any input is X/Z (as per the default case in the RTL).
// Includes functional assertions, change-parity assertion, and compact coverage.

module karnaugh_map_sva (input logic A, B, C, F);

  // Trigger on any input edge
  `define KM_CE (posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)

  // Functional correctness for known inputs
  property p_func_known;
    @(`KM_CE) !$isunknown({A,B,C}) |-> (F == (^ {A,B,C}));
  endproperty
  a_func_known: assert property (p_func_known)
    else $error("F != A^B^C for known inputs: A=%0b B=%0b C=%0b F=%0b", A,B,C,F);

  // Defined behavior for any X/Z on inputs (RTL default drives 0)
  property p_func_unknown;
    @(`KM_CE) $isunknown({A,B,C}) |-> (F == 1'b0);
  endproperty
  a_func_unknown: assert property (p_func_unknown)
    else $error("F not 0 when inputs contain X/Z: A=%b B=%b C=%b F=%b", A,B,C,F);

  // Output changes iff an odd number of inputs change between samples
  property p_change_parity;
    @(`KM_CE) $changed(F) == (^{$changed(A), $changed(B), $changed(C)});
  endproperty
  a_change_parity: assert property (p_change_parity)
    else $error("F change parity mismatch with input changes");

  // Full input-space coverage (with observed F)
  cover property (@(`KM_CE) {A,B,C}==3'b000 && F==1'b0);
  cover property (@(`KM_CE) {A,B,C}==3'b001 && F==1'b1);
  cover property (@(`KM_CE) {A,B,C}==3'b010 && F==1'b1);
  cover property (@(`KM_CE) {A,B,C}==3'b011 && F==1'b0);
  cover property (@(`KM_CE) {A,B,C}==3'b100 && F==1'b1);
  cover property (@(`KM_CE) {A,B,C}==3'b101 && F==1'b0);
  cover property (@(`KM_CE) {A,B,C}==3'b110 && F==1'b0);
  cover property (@(`KM_CE) {A,B,C}==3'b111 && F==1'b1);

  // Output toggle coverage
  cover property (@(`KM_CE) $rose(F));
  cover property (@(`KM_CE) $fell(F));

  // Single-bit toggle coverage (others stable) causing F toggle
  cover property (@(`KM_CE) $changed(A) && $stable(B) && $stable(C) && $changed(F));
  cover property (@(`KM_CE) $changed(B) && $stable(A) && $stable(C) && $changed(F));
  cover property (@(`KM_CE) $changed(C) && $stable(A) && $stable(B) && $changed(F));

endmodule

// Bind to DUT
bind karnaugh_map karnaugh_map_sva sva_kmap (.A(A), .B(B), .C(C), .F(F));