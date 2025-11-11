// SVA for add_sub. Bind this to the DUT.
// Key checks: functional correctness (with proper wrap), X-prop, no spurious OUT toggles,
// and concise functional coverage (op modes, overflow/underflow, a few edges).

module add_sub_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       SUB,
  input  logic [3:0] OUT
);

  // Helpers (explicit 5-bit arithmetic, then take low nibble)
  let sum5  = {1'b0, A} + {1'b0, B};
  let diff5 = {1'b0, B} - {1'b0, A};

  // Functional correctness (sample after delta to avoid races)
  ap_func: assert property (@(A or B or SUB) ##0 (OUT == (SUB ? diff5[3:0] : sum5[3:0])));

  // Known-ness: when inputs are known, OUT must be known
  ap_no_x: assert property (@(A or B or SUB) (!$isunknown({A,B,SUB})) |-> ##0 !$isunknown(OUT));

  // OUT only changes in response to input changes
  ap_no_spurious: assert property (@(A or B or SUB or OUT)
                                   $changed(OUT) |-> ($changed(A) || $changed(B) || $changed(SUB)));

  // Coverage: exercise both modes and wrap conditions
  cp_add:           cover property (@(A or B or SUB) (!SUB) ##0 (OUT == sum5[3:0]));
  cp_add_overflow:  cover property (@(A or B or SUB) (!SUB && sum5[4]));
  cp_sub:           cover property (@(A or B or SUB) ( SUB) ##0 (OUT == diff5[3:0]));
  cp_sub_underflow: cover property (@(A or B or SUB) ( SUB && diff5[4]));

  // A few edge cases
  cp_zero_zero: cover property (@(A or B or SUB) (A==4'h0 && B==4'h0));
  cp_max_max:   cover property (@(A or B or SUB) (A==4'hF && B==4'hF));
  cp_min_max:   cover property (@(A or B or SUB) (!SUB && A==4'h0 && B==4'hF));
  cp_max_min:   cover property (@(A or B or SUB) (!SUB && A==4'hF && B==4'h0));

endmodule

// Bind example (adjust instance pattern as needed):
// bind add_sub add_sub_sva sva_i (.A(A), .B(B), .SUB(SUB), .OUT(OUT));