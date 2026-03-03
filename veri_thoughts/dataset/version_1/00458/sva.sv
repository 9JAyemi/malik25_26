// SVA binders for mux4to1 and mux2to1
// Concise, combinational, 4-state exact checks, plus focused coverage.

module mux4to1_sva(
  input logic in0, in1, in2, in3,
  input logic [1:0] sel,
  input logic out,
  input logic w1, w2
);

  // Functional equivalence (delta-cycle settle)
  property p_mux4_func;
    ##0 out === (sel[1] ? (sel[0] ? in3 : in2) : (sel[0] ? in1 : in0));
  endproperty
  assert property (@(*) p_mux4_func);

  // Internal 2:1 stages correctness
  assert property (@(*) ##0 w1 === (sel[0] ? in1 : in0));
  assert property (@(*) ##0 w2 === (sel[0] ? in3 : in2));

  // 4-state merge (X/Z) behavior on LSB stage
  assert property (@(*) (sel[0] !== 1'b0 && sel[0] !== 1'b1) |-> ##0
                              ((in0 === in1) ? (w1 === in0) : $isunknown(w1)));
  assert property (@(*) (sel[0] !== 1'b0 && sel[0] !== 1'b1) |-> ##0
                              ((in2 === in3) ? (w2 === in2) : $isunknown(w2)));

  // 4-state merge behavior on MSB stage
  assert property (@(*) (sel[1] !== 1'b0 && sel[1] !== 1'b1) |-> ##0
                              ((w1 === w2) ? (out === w1) : $isunknown(out)));

  // Output follows selected input on change (same-delta)
  assert property (@(*) ( (sel==2'b00 && $changed(in0)) ||
                          (sel==2'b01 && $changed(in1)) ||
                          (sel==2'b10 && $changed(in2)) ||
                          (sel==2'b11 && $changed(in3)) )
                          |-> ##0 ($changed(out) &&
                                   out === (sel==2'b00 ? in0 :
                                            sel==2'b01 ? in1 :
                                            sel==2'b10 ? in2 : in3)));

  // Basic functional coverage
  cover property (@(*) sel==2'b00);
  cover property (@(*) sel==2'b01);
  cover property (@(*) sel==2'b10);
  cover property (@(*) sel==2'b11);

  // Cover both output values under each selection
  cover property (@(*) sel==2'b00 && out===1'b0);
  cover property (@(*) sel==2'b00 && out===1'b1);
  cover property (@(*) sel==2'b01 && out===1'b0);
  cover property (@(*) sel==2'b01 && out===1'b1);
  cover property (@(*) sel==2'b10 && out===1'b0);
  cover property (@(*) sel==2'b10 && out===1'b1);
  cover property (@(*) sel==2'b11 && out===1'b0);
  cover property (@(*) sel==2'b11 && out===1'b1);

  // Cover interesting X-merge scenarios
  cover property (@(*) (sel[0]===1'bx && in0!==in1 && $isunknown(w1)));
  cover property (@(*) (sel[0]===1'bx && in2!==in3 && $isunknown(w2)));
  cover property (@(*) (sel[1]===1'bx && w1!==w2 && $isunknown(out)));
  cover property (@(*) (sel[1]===1'bx && w1===w2 && out===w1));

endmodule

bind mux4to1 mux4to1_sva
  ( .in0(in0), .in1(in1), .in2(in2), .in3(in3),
    .sel(sel), .out(out), .w1(w1), .w2(w2) );

module mux2to1_sva(
  input logic in0, in1, sel, out
);
  // Functional equivalence (delta settle)
  assert property (@(*) ##0 out === (sel ? in1 : in0));

  // 4-state merge: unknown select
  assert property (@(*) (sel !== 1'b0 && sel !== 1'b1) |-> ##0
                              ((in0 === in1) ? (out === in0) : $isunknown(out)));

  // Coverage: select values and output values
  cover property (@(*) sel===1'b0);
  cover property (@(*) sel===1'b1);
  cover property (@(*) out===1'b0);
  cover property (@(*) out===1'b1);
  cover property (@(*) (sel===1'bx && in0!==in1 && $isunknown(out)));
  cover property (@(*) (sel===1'bx && in0===in1 && out===in0));
endmodule

bind mux2to1 mux2to1_sva (.*);