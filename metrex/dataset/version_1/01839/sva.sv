// SVA checker bound into the DUT scope (clockless concurrent assertions)
module three_input_and_sva;

  // Functional correctness of internal nets and output
  assert property (ab  === (a & b));
  assert property (bc  === (b & c));
  assert property (abc === (ab & c));
  assert property (out === abc);
  assert property (out === (a & b & c));

  // X/Z hygiene on all relevant signals
  assert property (!$isunknown({a,b,c,ab,bc,abc,out}));

  // State coverage: all 8 input combinations with expected output
  cover property (!a && !b && !c && !out);
  cover property (!a && !b &&  c && !out);
  cover property (!a &&  b && !c && !out);
  cover property (!a &&  b &&  c && !out);
  cover property ( a && !b && !c && !out);
  cover property ( a && !b &&  c && !out);
  cover property ( a &&  b && !c && !out);
  cover property ( a &&  b &&  c &&  out);

  // Output toggle coverage
  cover property ($rose(out));
  cover property ($fell(out));

endmodule

bind three_input_and three_input_and_sva sva();