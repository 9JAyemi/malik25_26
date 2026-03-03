// SVA checker for absolute_value
module absolute_value_sva (
  input  signed [31:0] in,
  input  signed [31:0] out
);
  function automatic signed [31:0] abs32(input signed [31:0] v);
    abs32 = (v < 0) ? -v : v;
  endfunction

  localparam signed [31:0] MIN_INT = 32'sh8000_0000;

  default clocking cb @(in or out); endclocking

  // Functional correctness for known inputs
  ap_correct_known: assert property ( !$isunknown(in) |-> (out === abs32(in)) );

  // Output must be known whenever input is known
  ap_knownness:     assert property ( !$isunknown(in) |-> !$isunknown(out) );

  // Non-negativity except the MIN_INT overflow corner
  ap_nonneg:        assert property ( (!$isunknown(in) && in != MIN_INT) |-> ($signed(out) >= 0) );

  // Explicit MIN_INT corner-case behavior
  ap_minint:        assert property ( (in === MIN_INT) |-> (out === MIN_INT) );

  // Algebraic invariant: |x| == |-x| (helps catch sign handling mistakes)
  ap_symmetry:      assert property ( !$isunknown(in) |-> (out === abs32(-in)) );

  // Coverage
  cv_zero: cover property ( !$isunknown(in) && (in == 32'sd0) );
  cv_pos:  cover property ( !$isunknown(in) && ($signed(in) > 0) );
  cv_neg:  cover property ( !$isunknown(in) && ($signed(in) < 0) && (in != MIN_INT) );
  cv_min:  cover property ( in === MIN_INT );
endmodule

// Bind into the DUT
bind absolute_value absolute_value_sva abs_val_sva_i (.in(in), .out(out));