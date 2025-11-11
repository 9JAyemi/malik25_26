// SVA for three_input_gate: concise, full functional checks and coverage
module three_input_gate_sva (input logic A1, A2, B1, X);

  function automatic logic all_ones(input logic a1,a2,b1);
    return (a1 === 1'b1) && (a2 === 1'b1) && (b1 === 1'b1);
  endfunction

  // Functional equivalence (4-state aware) after delta on any input change
  assert property (@(A1 or A2 or B1) ##0 (X === all_ones(A1,A2,B1)));

  // Output becomes known after inputs change
  assert property (@(A1 or A2 or B1) ##0 !$isunknown(X));

  // No spurious output change without proximate input change (same or previous sample)
  assert property (@(A1 or A2 or B1 or X)
                   $changed(X) |->
                     ($changed(A1) || $changed(A2) || $changed(B1) ||
                      (!$isunknown($past(1'b1)) &&
                       ($past($changed(A1)) || $past($changed(A2)) || $past($changed(B1))))));

  // Edge-specific checks (single-input enable/disable when others are 1)
  assert property (@(A1) $rose(A1) && (A2===1 && B1===1) |-> ##0 (X==1));
  assert property (@(A2) $rose(A2) && (A1===1 && B1===1) |-> ##0 (X==1));
  assert property (@(B1) $rose(B1) && (A1===1 && A2===1) |-> ##0 (X==1));
  assert property (@(A1) $fell(A1) && (A2===1 && B1===1) |-> ##0 (X==0));
  assert property (@(A2) $fell(A2) && (A1===1 && B1===1) |-> ##0 (X==0));
  assert property (@(B1) $fell(B1) && (A1===1 && A2===1) |-> ##0 (X==0));

  // Functional coverage: all input combinations and resulting X
  cover property (@(A1 or A2 or B1) ##0 (A1===0 && A2===0 && B1===0 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===0 && A2===0 && B1===1 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===0 && A2===1 && B1===0 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===0 && A2===1 && B1===1 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===1 && A2===0 && B1===0 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===1 && A2===0 && B1===1 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===1 && A2===1 && B1===0 && X==0));
  cover property (@(A1 or A2 or B1) ##0 (A1===1 && A2===1 && B1===1 && X==1));

  // Output transition coverage
  cover property (@(A1 or A2 or B1 or X) $rose(X));
  cover property (@(A1 or A2 or B1 or X) $fell(X));

endmodule

bind three_input_gate three_input_gate_sva sva_i(.A1(A1),.A2(A2),.B1(B1),.X(X));