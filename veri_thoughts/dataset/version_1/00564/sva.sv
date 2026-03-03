// SVA checker for four_way_min (bindable, clockless, concise yet thorough)
module four_way_min_sva
  #(parameter WIDTH=8)
  (input  logic [WIDTH-1:0] a, b, c, d,
   input  logic [WIDTH-1:0] min,
   input  logic [WIDTH-1:0] ab_min, cd_min, abcd_min);

  // 2-way and 4-way mins (use 4-state-aware '<'; gated by known inputs)
  function automatic logic [WIDTH-1:0] f_min2 (input logic [WIDTH-1:0] x, y);
    return (x < y) ? x : y;
  endfunction
  function automatic logic [WIDTH-1:0] f_min4 (input logic [WIDTH-1:0] w, x, y, z);
    return f_min2(f_min2(w, x), f_min2(y, z));
  endfunction

  // End-to-end correctness when inputs are known
  property p_min_correct;
    @(a or b or c or d or min)
      !$isunknown({a,b,c,d}) |-> (min == f_min4(a,b,c,d));
  endproperty
  assert property (p_min_correct);

  // Stage-wise correctness (also gated for known operands)
  assert property (@(a or b or ab_min)           !$isunknown({a,b})           |-> (ab_min   == f_min2(a,b)));
  assert property (@(c or d or cd_min)           !$isunknown({c,d})           |-> (cd_min   == f_min2(c,d)));
  assert property (@(ab_min or cd_min or abcd_min) !$isunknown({ab_min,cd_min}) |-> (abcd_min == f_min2(ab_min,cd_min)));
  assert property (@(abcd_min or min)            !$isunknown(abcd_min)        |-> (min      == abcd_min));

  // Sanity: min is no greater than each input when inputs are known
  assert property (@(a or b or c or d or min)
                   !$isunknown({a,b,c,d}) |-> (min <= a && min <= b && min <= c && min <= d));

  // ----------------------------------
  // Coverage (branching, winners, ties)
  // ----------------------------------

  // Pairwise comparator branching
  cover property (@(a or b) !$isunknown({a,b}) && (a <  b));
  cover property (@(a or b) !$isunknown({a,b}) && (a >= b));
  cover property (@(c or d) !$isunknown({c,d}) && (c <  d));
  cover property (@(c or d) !$isunknown({c,d}) && (c >= d));

  // Second-stage comparator outcomes
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) &&
                  (f_min2(a,b) <  f_min2(c,d)));
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) &&
                  (f_min2(a,b) == f_min2(c,d)));
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) &&
                  (f_min2(a,b) >  f_min2(c,d)));

  // Unique winners (strict minima)
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (a<b && a<c && a<d) && (min==a));
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (b<a && b<c && b<d) && (min==b));
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (c<a && c<b && c<d) && (min==c));
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (d<a && d<b && d<c) && (min==d));

  // Tie behaviors per implementation (< prefers right operand on tie)
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (a==b) && (a<c) && (a<d) && (min==b)); // ab tie -> pick b
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (c==d) && (c<a) && (c<b) && (min==d)); // cd tie -> pick d

  // All equal
  cover property (@(a or b or c or d) !$isunknown({a,b,c,d}) && (a==b && b==c && c==d) && (min==a));

endmodule

// Bind into the DUT; connects to internals by name
bind four_way_min four_way_min_sva #(.WIDTH(8)) four_way_min_sva_i (.*);