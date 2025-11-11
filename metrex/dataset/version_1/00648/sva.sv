// SVA for mux_2to1 (clockless, event-driven, concise and complete)
module mux_2to1_sva (input logic A, B, S, Y);

  // Functional equivalence (evaluate after combinational updates)
  property p_func;
    @(A or B or S or Y)
      1'b1 |-> ##0 ( Y === ((S===1'b1) ? B :
                            (S===1'b0) ? A : 1'b0) );
  endproperty
  assert property (p_func);

  // Known inputs imply known output
  assert property (@(A or B or S or Y)
                   (!$isunknown({A,B,S})) |-> ##0 (!$isunknown(Y)));

  // No spurious output changes (Y only changes if a driving input changes)
  assert property (@(A or B or S or Y)
                   $changed(Y) |-> ($changed(A) || $changed(B) || $changed(S)));

  // Unselected input must not affect Y
  assert property (@(A or B or S or Y)
                   (S===1'b0 && !$changed(S) && !$changed(A) && $changed(B)) |-> ##0 !$changed(Y));
  assert property (@(A or B or S or Y)
                   (S===1'b1 && !$changed(S) && !$changed(B) && $changed(A)) |-> ##0 !$changed(Y));

  // Coverage: data follows through both selects, select edges, and X/Z on S
  cover property (@(A or B or S or Y)
                  (S===1'b0 && $changed(A) && !$changed(S)) ##0 $changed(Y));
  cover property (@(A or B or S or Y)
                  (S===1'b1 && $changed(B) && !$changed(S)) ##0 $changed(Y));
  cover property (@(A or B or S or Y) $rose(S) ##0 (Y===B));
  cover property (@(A or B or S or Y) $fell(S) ##0 (Y===A));
  cover property (@(A or B or S or Y) $isunknown(S) ##0 (Y===1'b0));

endmodule

// Bind example:
// bind mux_2to1 mux_2to1_sva u_mux_2to1_sva(.A(A), .B(B), .S(S), .Y(Y));