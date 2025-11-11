// Bindable SVA for adler_checksum
// Focus: reset behavior, accumulators, checksum compute, modes, output mirroring, and coverage.

module adler_checksum_sva;

  // Use DUT scope names via bind
  // default clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  localparam int W = $bits(checksum_reg);

  // Helpers (operate in a wide domain, then truncate to W bits)
  function automatic logic [W-1:0] exp_chk(input logic [W-1:0] ss, input logic [W-1:0] s);
    logic [255:0] ext_ss = {{(256-W){1'b0}}, ss};
    logic [255:0] ext_s  = {{(256-W){1'b0}}, s};
    logic [255:0] ext_p  = logic [255:0]'(prime);
    logic [255:0] pre    = (ext_ss << 16) + ext_s;
    logic [255:0] modv   = (ext_p != 0) ? (pre % ext_p) : pre;
    return modv[W-1:0];
  endfunction

  // Reset clears (override default disable)
  ap_reset_clears: assert property (@(posedge clk) disable iff (1'b0)
    reset |=> (data_reg==0 && checksum_reg==0 && sum_reg==0 &&
               sum_of_squares_reg==0 && checksum_calc==0 && checksum_match_reg==0));

  // Output mirroring
  ap_map_data_out:      assert property (data_out      == data_reg);
  ap_map_valid_out:     assert property (valid_out     == valid_in);
  ap_map_checksum_out:  assert property (checksum_out  == checksum_reg);
  ap_map_checksum_match:assert property (checksum_match== checksum_match_reg);

  // Accumulator hold/update
  ap_hold_when_no_valid: assert property (!valid_in |-> $stable({data_reg,sum_reg,sum_of_squares_reg}));
  ap_update_on_valid:    assert property ( valid_in |=> ( data_reg == $past(data_in)
                                                       && sum_reg == ( $past(sum_reg) + $past(data_in) )[W-1:0]
                                                       && sum_of_squares_reg == ( $past(sum_of_squares_reg)
                                                                                 + ($past(data_in)*$past(data_in)) )[W-1:0] ));

  // Checksum compute (from pre-state sums)
  ap_checksum_compute: assert property ( start |=> checksum_reg == exp_chk($past(sum_of_squares_reg), $past(sum_reg)) );

  // Checksum reg updates only when start was asserted in the prior cycle
  ap_checksum_updates_only_on_prev_start: assert property ( !$past(start) |-> $stable(checksum_reg) );

  // Mode behavior on start
  ap_checker_mode_match: assert property ( start && (checksum_in != '0)
                                           |=> checksum_match_reg == ($past(checksum_in) == $past(checksum_reg)) );
  ap_generator_mode_calc: assert property ( start && (checksum_in == '0)
                                            |=> checksum_calc == $past(checksum_reg) );

  // checksum_match_reg updates only on prior start
  ap_match_updates_only_on_prev_start: assert property ( !$past(start) |-> $stable(checksum_match_reg) );

  // Basic X/Z sanitization on outputs
  ap_no_x_outs: assert property ( !$isunknown({data_out,valid_out,checksum_out,checksum_match}) );

  // Coverage
  cv_reset_release:        cover property (@(posedge clk) disable iff (1'b0) reset ##1 !reset);
  cv_three_valids:         cover property ( valid_in [*3] );
  cv_start_generator:      cover property ( start && (checksum_in == '0) );
  cv_start_checker:        cover property ( start && (checksum_in != '0) );
  cv_start_with_valid:     cover property ( valid_in && start );
  cv_checker_match:        cover property ( start && (checksum_in != '0) ##1 checksum_match );
  cv_checker_mismatch:     cover property ( start && (checksum_in != '0) ##1 !checksum_match );

  // Optional: intended spec check (may fail on current RTL due to double-NB bug on checksum_reg)
  ap_intended_checker_uses_computed_checksum: assert property (
    start && (checksum_in != '0) |=> checksum_match_reg == ($past(checksum_in) == exp_chk($past(sum_of_squares_reg), $past(sum_reg))) );

endmodule

// Bind into all instances of adler_checksum
bind adler_checksum adler_checksum_sva sva_adler_checksum();