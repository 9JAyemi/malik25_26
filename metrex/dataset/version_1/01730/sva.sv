// SVA checkers and binds for min_finder and pipeline_stage

// Checker for pipeline_stage (parameterized)
module pipeline_stage_sva #(parameter WIDTH=8) (
  input  logic [WIDTH-1:0] in_a,
  input  logic [WIDTH-1:0] in_b,
  input  logic [WIDTH-1:0] out
);
  // Functional correctness
  assert property (@(*) out == ((in_a < in_b) ? in_a : in_b));

  // Tie behavior
  assert property (@(*) (in_a == in_b) |-> (out == in_b));

  // No X/Z propagation when inputs are known
  assert property (@(*) !$isunknown({in_a,in_b}) |-> !$isunknown(out));

  // Basic functional coverage
  cover property (@(*) (in_a < in_b) && (out == in_a));
  cover property (@(*) (in_a > in_b) && (out == in_b));
  cover property (@(*) (in_a == in_b) && (out == in_b));
endmodule

bind pipeline_stage pipeline_stage_sva #(.WIDTH(WIDTH))
  pipeline_stage_sva_b(.in_a(in_a), .in_b(in_b), .out(out));


// Checker for min_finder (accesses internal nets via bind)
module min_finder_sva (
  input logic [7:0] a, b, c, d,
  input logic [7:0] ab_min, cd_min, abcd_min,
  input logic [7:0] min
);
  // Stage-by-stage correctness
  assert property (@(*) ab_min   == ((a < b) ? a : b));
  assert property (@(*) cd_min   == ((c < d) ? c : d));
  assert property (@(*) abcd_min == ((ab_min < cd_min) ? ab_min : cd_min));
  assert property (@(*) min == abcd_min);

  // End-to-end equivalence to min(a,b,c,d)
  assert property (@(*)
    min == ( ((a<b)?a:b) < ((c<d)?c:d) ? ((a<b)?a:b) : ((c<d)?c:d) )
  );

  // Sanity: min is no greater than any input and equals one of them
  assert property (@(*) (min <= a) && (min <= b) && (min <= c) && (min <= d));
  assert property (@(*) (min == a) || (min == b) || (min == c) || (min == d));

  // No X/Z propagation when inputs are known
  assert property (@(*) !$isunknown({a,b,c,d}) |-> !$isunknown(min));

  // Coverage: each input wins (with tie-break consistent with DUT)
  cover property (@(*) (a < b) && (a < c) && (a < d) && (min == a));
  cover property (@(*) (b <= a) && (b < c) && (b < d) && (min == b));
  cover property (@(*) (c < d) && (c < a) && (c < b) && (min == c));
  cover property (@(*) (d <= c) && (d < a) && (d < b) && (min == d));

  // Coverage: tie behaviors and branch selection
  cover property (@(*) (a == b) && (b < c) && (b < d) && (min == b)); // left-stage tie -> b
  cover property (@(*) (c == d) && (d < a) && (d < b) && (min == d)); // right-stage tie -> d
  cover property (@(*) (ab_min == cd_min) && (min == cd_min));        // final-stage tie -> right

  // Coverage: extremes and all-equal case
  cover property (@(*) (min == 8'h00));
  cover property (@(*) (a == b) && (b == c) && (c == d) && (min == d)); // all equal -> d
  cover property (@(*) (a==8'hFF && b==8'hFF && c==8'hFF && d==8'hFF && min==8'hFF));
endmodule

bind min_finder min_finder_sva min_finder_sva_b(
  .a(a), .b(b), .c(c), .d(d),
  .ab_min(ab_min), .cd_min(cd_min), .abcd_min(abcd_min),
  .min(min)
);