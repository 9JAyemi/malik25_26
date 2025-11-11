// SVA bind file for module eight_to_one
// Concise, high-quality checks and corner-case coverage

module eight_to_one_sva (
  input       y,
  input [3:0] a1, a2, a3, b1,
  input       vpwr, vgnd, vpb, vnb
);
  // Power-good and combinational sampling
  logic pgood;
  always_comb pgood = (vpwr===1'b1 && vgnd===1'b0 && vpb===1'b1 && vnb===1'b0);

  default clocking cb @(*) endclocking
  default disable iff (!pgood)

  // Computations for checking
  logic [5:0] true_sum;    // full-precision sum (0..60)
  logic [4:0] sum_mod32;   // DUT's truncated sum
  always_comb begin
    true_sum  = a1 + a2 + a3 + b1;
    sum_mod32 = true_sum[4:0];
  end

  // Basic sanity (no X/Z and y is 0/1) when power is good
  ap_inputs_known: assert (!$isunknown({a1,a2,a3,b1}));
  ap_y_known:      assert (!$isunknown(y));
  ap_y_is_bool:    assert (y inside {1'b0,1'b1});

  // Functional equivalence to current implementation (mod-32 threshold)
  ap_y_matches_mod32_thresh: assert (y == (sum_mod32 >= 6'd10));

  // Flag potential width truncation bug: full sum must fit 5 bits (optional tighten)
  ap_no_overflow: assert (true_sum < 6'd32);

  // Spec-level check when no overflow occurs
  ap_y_matches_true_thresh_when_no_overflow:
    assert ( (true_sum < 6'd32) |-> (y == (true_sum >= 6'd10)) );

  // Corner-case coverage
  cp_below_thresh:  cover (true_sum == 6'd9  && y == 1'b0);
  cp_at_thresh:     cover (true_sum == 6'd10 && y == 1'b1);
  cp_above_thresh:  cover (true_sum == 6'd11 && y == 1'b1);
  cp_zero:          cover (true_sum == 6'd0  && y == 1'b0);
  cp_overflow:      cover (true_sum >= 6'd32);
  cp_all_max:       cover (a1==4'hF && a2==4'hF && a3==4'hF && b1==4'hF); // worst-case sum

endmodule

bind eight_to_one eight_to_one_sva sva_eight_to_one (.*);