// SVA for smallest_number
module smallest_number_sva #(parameter int W=4)
(
  input logic [W-1:0] A, B, C,
  input logic [W-1:0] smallest
);

  function automatic logic [W-1:0] f_min3 (input logic [W-1:0] a,b,c);
    if (a<=b && a<=c) f_min3 = a;
    else if (b<=a && b<=c) f_min3 = b;
    else f_min3 = c;
  endfunction

  // Correctness: output is the min when inputs are known
  property p_min_value;
    @(A or B or C or smallest) disable iff ($isunknown({A,B,C}))
      1'b1 |-> ##0 (smallest == f_min3(A,B,C));
  endproperty
  assert property (p_min_value);

  // Priority/branch checks (including tie resolution)
  property p_pick_A;
    @(A or B or C or smallest) disable iff ($isunknown({A,B,C}))
      (A<=B && A<=C) |-> ##0 (smallest == A);
  endproperty
  assert property (p_pick_A);

  property p_pick_B;
    @(A or B or C or smallest) disable iff ($isunknown({A,B,C}))
      (!(A<=B && A<=C) && (B<=A && B<=C)) |-> ##0 (smallest == B);
  endproperty
  assert property (p_pick_B);

  property p_pick_C;
    @(A or B or C or smallest) disable iff ($isunknown({A,B,C}))
      (!(A<=B && A<=C) && !(B<=A && B<=C)) |-> ##0 (smallest == C);
  endproperty
  assert property (p_pick_C);

  // X-propagation sanity: known inputs -> known output
  property p_known_out_when_known_in;
    @(A or B or C or smallest)
      (!$isunknown({A,B,C})) |-> ##0 (!$isunknown(smallest));
  endproperty
  assert property (p_known_out_when_known_in);

  // Coverage: unique minima, tie cases, and extreme
  cover property (@(A or B or C) (A<B && A<C));      // unique A min
  cover property (@(A or B or C) (B<A && B<C));      // unique B min
  cover property (@(A or B or C) (C<A && C<B));      // unique C min
  cover property (@(A or B or C) (A==B && A<C));     // A==B < C (A chosen)
  cover property (@(A or B or C) (A==C && A<B));     // A==C < B (A chosen)
  cover property (@(A or B or C) (B==C && B<A));     // B==C < A (B chosen)
  cover property (@(A or B or C) (A==B && B==C));    // all equal
  cover property (@(A or B or C) (smallest==0));     // min at 0

endmodule

// Bind to DUT
bind smallest_number smallest_number_sva sva_smallest_number(.A(A), .B(B), .C(C), .smallest(smallest));