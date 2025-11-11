// SVA checker for max_value
// Bind into DUT to access internal max_val as well.
module max_value_sva (
  input  logic [7:0]  A, B, C, D,
  input  logic [15:0] out,
  input  logic [7:0]  max_val
);

  // Sample on any activity of inputs or output (purely combinational DUT)
  default clocking cb @ (A or B or C or D or out); endclocking

  // Golden model of the max (uses same strict '>' semantics as DUT)
  function automatic logic [7:0] max2 (input logic [7:0] x, y);
    max2 = (x > y) ? x : y;
  endfunction
  function automatic logic [7:0] max4 (input logic [7:0] a, b, c, d);
    logic [7:0] m;
    m    = max2(a, b);
    m    = max2(m, c);
    max4 = max2(m, d);
  endfunction

  // X/Z hygiene
  ap_known_inputs: assert property (!$isunknown({A,B,C,D})))
    else $error("max_value: inputs contain X/Z");
  ap_known_out:    assert property (!$isunknown(out))
    else $error("max_value: out contains X/Z");

  // Functional correctness
  ap_low_zero:     assert property (out[7:0] == 8'h00)
    else $error("max_value: low byte not zero");
  ap_hi_is_max:    assert property (out[15:8] == max4(A,B,C,D))
    else $error("max_value: high byte not max(A,B,C,D)");
  ap_internal_consistency: assert property (max_val == out[15:8])
    else $error("max_value: internal max_val != out[15:8]");
  ap_full_vector:  assert property (out == {max4(A,B,C,D), 8'h00})
    else $error("max_value: out != {max,8'h00}");

  // Coverage: each winner, ties, extremes
  cv_win_A:      cover property (A>B && A>C && A>D && out[15:8]==A);
  cv_win_B:      cover property (B>A && B>C && B>D && out[15:8]==B);
  cv_win_C:      cover property (C>A && C>B && C>D && out[15:8]==C);
  cv_win_D:      cover property (D>A && D>B && D>C && out[15:8]==D);
  cv_tie_AB:     cover property (A==B && A>=C && A>=D && out[15:8]==A);
  cv_tie_CD:     cover property (C==D && C>=A && C>=B && out[15:8]==C);
  cv_all_equal:  cover property (A==B && B==C && C==D && out[15:8]==A);
  cv_min:        cover property (out[15:8] == 8'h00);
  cv_max:        cover property (out[15:8] == 8'hFF);

endmodule

// Bind into the DUT (connects to internal max_val as well)
bind max_value max_value_sva u_max_value_sva (.*);