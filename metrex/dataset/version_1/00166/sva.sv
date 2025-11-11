// SVA for sky130_fd_sc_lp__a32oi
// Function: Y = ~((A1 & A2 & A3) | (B1 & B2))

module sky130_fd_sc_lp__a32oi_sva (
  input logic A1, A2, A3, B1, B2,
  input logic Y
);
  function automatic bit known5 (logic [4:0] v);
    return !$isunknown(v);
  endfunction

  // Functional equivalence (sample on any relevant change; settle with ##0)
  property p_func;
    @(A1 or A2 or A3 or B1 or B2 or Y)
      known5({A1,A2,A3,B1,B2}) |-> ##0
        (Y === ~((A1 & A2 & A3) | (B1 & B2)));
  endproperty
  assert property (p_func);

  // Output must be known when inputs are known
  property p_known_out;
    @(A1 or A2 or A3 or B1 or B2 or Y)
      known5({A1,A2,A3,B1,B2}) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_known_out);

  // Sanity implications
  property p_any_and_true_then_Y0;
    @(A1 or A2 or A3 or B1 or B2 or Y)
      ((A1 & A2 & A3) || (B1 & B2)) |-> ##0 (Y === 1'b0);
  endproperty
  assert property (p_any_and_true_then_Y0);

  property p_both_and_false_then_Y1;
    @(A1 or A2 or A3 or B1 or B2 or Y)
      (!(A1 & A2 & A3) && !(B1 & B2)) |-> ##0 (Y === 1'b1);
  endproperty
  assert property (p_both_and_false_then_Y1);

  // No spurious X on Y unless some input is X/Z
  property p_no_spurious_x_on_y;
    @(A1 or A2 or A3 or B1 or B2 or Y)
      (!$isunknown(Y)) or (!$isunknown({A1,A2,A3,B1,B2}));
  endproperty
  assert property (p_no_spurious_x_on_y);

  // Coverage: all functional classes and Y edges
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y)
                  (!(A1 & A2 & A3) && !(B1 & B2)) ##0 (Y == 1'b1)); // both false
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y)
                  ((A1 & A2 & A3) && !(B1 & B2)) ##0 (Y == 1'b0)); // only 3-input true
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y)
                  (!(A1 & A2 & A3) && (B1 & B2)) ##0 (Y == 1'b0)); // only 2-input true
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y)
                  ((A1 & A2 & A3) && (B1 & B2)) ##0 (Y == 1'b0));  // both true
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) $rose(Y));
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) $fell(Y));
endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__a32oi sky130_fd_sc_lp__a32oi_sva
  (.A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2), .Y(Y));