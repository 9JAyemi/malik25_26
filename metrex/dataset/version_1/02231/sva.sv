// Assertions for half_subtractor and full_subtractor.
// Bind these into the DUT; they are clockless and trigger on input edges.

module hs_sva;
  // Sample on any input edge
  // Functional correctness vs spec
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   !$isunknown({a,b}) |-> (diff == (a ^ b)));
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   !$isunknown({a,b}) |-> (bout == (~a & b))); // borrow spec

  // Outputs must not go X/Z when inputs are known
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   !$isunknown({a,b}) |-> !$isunknown({diff,bout}));

  // Input combination coverage (all 4)
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b} == 2'b00);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b} == 2'b01);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b} == 2'b10);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b} == 2'b11);
endmodule

module fs_sva;
  // Sample on any input edge
  // Full subtractor spec
  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin)
                   !$isunknown({a,b,bin}) |-> (diff == (a ^ b ^ bin)));
  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin)
                   !$isunknown({a,b,bin}) |-> (bout == ((~a & b) | ((~(a ^ b)) & bin))));

  // Outputs must not go X/Z when inputs are known
  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin)
                   !$isunknown({a,b,bin}) |-> !$isunknown({diff,bout}));

  // Check internal ripple structure correctness (bind has scope to internals)
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   temp_diff1 == (a ^ b));
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   temp_bout1 == (~a & b)); // half-sub borrow spec
  assert property (@(posedge temp_diff1 or negedge temp_diff1 or posedge bin or negedge bin)
                   temp_diff2 == (temp_diff1 ^ bin));
  assert property (@(posedge temp_diff1 or negedge temp_diff1 or posedge bin or negedge bin)
                   temp_bout2 == ((~temp_diff1) & bin)); // half-sub borrow spec
  assert property (@(posedge temp_bout1 or negedge temp_bout1 or posedge temp_bout2 or negedge temp_bout2)
                   bout == (temp_bout1 | temp_bout2));

  // Input combination coverage (all 8)
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b000);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b001);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b010);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b011);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b100);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b101);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b110);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge bin or negedge bin) {a,b,bin} == 3'b111);
endmodule

// Bind into all instances of the DUTs
bind half_subtractor hs_sva hs_sva_i();
bind full_subtractor fs_sva fs_sva_i();