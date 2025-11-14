// SVA for priority_encoder_4to2
// Binds assertions/coverage to the DUT, using a clockless $global_clock

module priority_encoder_4to2_sva (
  input logic a, b, c, d,
  input logic x, y
);

  default clocking cb @($global_clock); endclocking

  // Outputs must be known; ignore cycles with unknown inputs to avoid false failures
  assert property (disable iff ($isunknown({a,b,c,d})) ! $isunknown({x,y}));

  // Functional equivalence (pair {y,x} is the 2-bit encoded result)
  assert property (disable iff ($isunknown({a,b,c,d}))
                   {y,x} == (a ? 2'b00 :
                             b ? 2'b01 :
                             c ? 2'b10 :
                             d ? 2'b11 : 2'b00));

  // Winner-specific priority checks
  assert property (a                    |-> {y,x} == 2'b00);
  assert property (!a && b              |-> {y,x} == 2'b01);
  assert property (!a && !b && c        |-> {y,x} == 2'b10);
  assert property (!a && !b && !c && d  |-> {y,x} == 2'b11);
  assert property (!a && !b && !c && !d |-> {y,x} == 2'b00);

  // No spurious output changes when inputs are stable
  assert property ($stable({a,b,c,d}) |-> $stable({y,x}));

  // Coverage: each priority winner and idle
  cover property (a);
  cover property (!a && b);
  cover property (!a && !b && c);
  cover property (!a && !b && !c && d);
  cover property (!a && !b && !c && !d);

  // Coverage: overlapping requests to exercise priority resolution
  cover property (a && (b || c || d));
  cover property (!a && b && (c || d));
  cover property (!a && !b && c && d);

  // Coverage: all encoded outputs observed
  cover property ({y,x} == 2'b00);
  cover property ({y,x} == 2'b01);
  cover property ({y,x} == 2'b10);
  cover property ({y,x} == 2'b11);

endmodule

bind priority_encoder_4to2 priority_encoder_4to2_sva sva_i (
  .a(a), .b(b), .c(c), .d(d),
  .x(x), .y(y)
);