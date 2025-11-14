// SVA for Span12Mux_v11
module Span12Mux_v11_sva(input logic [11:0] I, input logic O);

  // Golden functionality (matches DUT ternary semantics incl. X behavior)
  assert property (@(*)) O === (I[11] ? I[10] : I[11]);

  // O must not depend on I[9:0]
  assert property (@(*)) ($stable(I[11:10]) && !$stable(I[9:0])) |-> $stable(O);

  // O can only change when I[11] or I[10] changes
  assert property (@(*)) !$stable(O) |-> (!$stable(I[11]) || !$stable(I[10]));

  // Known-inputs imply known output
  assert property (@(*)) (!$isunknown(I[11]) && !$isunknown(I[10])) |-> !$isunknown(O);

  // Functional coverage of all care cases
  cover property (@(*)) (!I[11]            && O===1'b0);
  cover property (@(*)) ( I[11] && !I[10]  && O===1'b0);
  cover property (@(*)) ( I[11] &&  I[10]  && O===1'b1);

  // X-behavior coverage when select is unknown
  cover property (@(*)) (I[11]===1'bx && $isunknown(O));

  // Output toggle coverage
  cover property (@(posedge O));
  cover property (@(negedge O));

endmodule

bind Span12Mux_v11 Span12Mux_v11_sva sva_inst(.I(I), .O(O));