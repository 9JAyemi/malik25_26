// SVA for Span12Mux_s5_h
module Span12Mux_s5_h_sva(
  input logic [3:0]  I,
  input logic [11:0] A, B, C, D, E,
  input logic [11:0] O
);
  // Core functional check (sample after a delta to allow comb. settle)
  property p_mux_functional;
    @(I or A or B or C or D or E)
      1'b1 |-> ##0 (
        (I == 4'b0000 && O === A) ||
        (I == 4'b0001 && O === B) ||
        (I == 4'b0010 && O === C) ||
        (I == 4'b0011 && O === D) ||
        (I == 4'b0100 && O === E) ||
        ((!(I inside {4'b0000,4'b0001,4'b0010,4'b0011,4'b0100}) || $isunknown(I)) && O === 12'b0)
      );
  endproperty
  a_mux_functional: assert property (p_mux_functional);

  // No X/Z on O when select and the selected input are known
  property p_no_x_on_O_when_inputs_known;
    @(I or A or B or C or D or E)
      ((I==4'b0000 && !$isunknown(A)) ||
       (I==4'b0001 && !$isunknown(B)) ||
       (I==4'b0010 && !$isunknown(C)) ||
       (I==4'b0011 && !$isunknown(D)) ||
       (I==4'b0100 && !$isunknown(E)) ||
       (! (I inside {4'b0000,4'b0001,4'b0010,4'b0011,4'b0100}) && !$isunknown(I)))
      |-> ##0 (!$isunknown(O));
  endproperty
  a_no_x_on_O_when_inputs_known: assert property (p_no_x_on_O_when_inputs_known);

  // Coverage: each select and default path observed
  cover property (@(I) I == 4'b0000);
  cover property (@(I) I == 4'b0001);
  cover property (@(I) I == 4'b0010);
  cover property (@(I) I == 4'b0011);
  cover property (@(I) I == 4'b0100);
  cover property (@(I) !(I inside {4'b0000,4'b0001,4'b0010,4'b0011,4'b0100}));
  cover property (@(I) $isunknown(I)); // default due to X/Z on I
endmodule

bind Span12Mux_s5_h Span12Mux_s5_h_sva sva_mux (.I(I), .A(A), .B(B), .C(C), .D(D), .E(E), .O(O));