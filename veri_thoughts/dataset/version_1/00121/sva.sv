// SVA for and_gate
// Bindable, concise, and with functional checks + coverage

module and_gate_sva (input logic a, b, y);

  // Functional equivalence (4-state aware)
  always_comb
    assert (y === (a & b))
      else $error("and_gate: y != a & b (a=%b b=%b y=%b)", a,b,y);

  // Output settles in same delta after any input change
  assert property (@(a or b) 1 |-> ##0 (y === (a & b)));

  // If inputs are known, output must be known and correct
  always_comb if (!$isunknown({a,b})) begin
    assert (!$isunknown(y)) else $error("and_gate: y is X/Z with known inputs (a=%b b=%b y=%b)",a,b,y);
    assert (y == (a & b)) else $error("and_gate: wrong y with known inputs (a=%b b=%b y=%b)",a,b,y);
  end

  // Edge correctness
  assert property (@(posedge y)  a && b)
    else $error("and_gate: y rose without both inputs high (a=%b b=%b y=%b)",a,b,y);
  assert property (@(negedge y) (!a || !b))
    else $error("and_gate: y fell while both inputs high (a=%b b=%b y=%b)",a,b,y);

  // No spurious output toggle without an input toggle
  assert property (@(a or b or y) $changed(y) |-> ($changed(a) || $changed(b)))
    else $error("and_gate: y changed without a/b change (a=%b b=%b y=%b)",a,b,y);

  // Coverage: truth table
  cover property (@(a or b) ##0 (!a && !b && !y));
  cover property (@(a or b) ##0 (!a &&  b && !y));
  cover property (@(a or b) ##0 ( a && !b && !y));
  cover property (@(a or b) ##0 ( a &&  b &&  y));

  // Coverage: output edges under correct conditions
  cover property (@(posedge y)  a && b);
  cover property (@(negedge y) (!a || !b));

endmodule

bind and_gate and_gate_sva and_gate_sva_i (.a(a), .b(b), .y(y));