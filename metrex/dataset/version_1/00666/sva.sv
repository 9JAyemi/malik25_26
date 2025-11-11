// SVA for dffs_37: synchronous set to all-ones, else q<=d

module dffs_37_sva (
  input  logic        clk,
  input  logic        set,
  input  logic [36:0] d,
  input  logic [36:0] q
);
  default clocking cb @(posedge clk); endclocking

  localparam logic [36:0] ALL1 = {37{1'b1}};
  let past_valid = $past(1'b1, 1, 0);

  // Core functional correctness: next q equals (set ? ALL1 : d) sampled at prior edge
  a_core: assert property (past_valid |-> ( $past(set) ? (q == ALL1) : (q == $past(d)) ))
    else $error("q update mismatch: set=%0b d(prev)=%0h q=%0h", $past(set), $past(d), q);

  // Sanity: no X/Z on key signals after first sampled edge
  a_no_x: assert property (past_valid |-> (!$isunknown(set) && !$isunknown(d) && !$isunknown(q)))
    else $error("X/Z detected on set/d/q");

  // Stability when inputs unchanged and set=0: q holds previous value
  a_hold: assert property (past_valid && !$past(set) && ($past(d) == $past($past(d))) |-> (q == $past(q)))
    else $error("q changed despite stable d and set=0");

  // Coverage: observe set path taken (q driven to ALL1)
  c_set_path:   cover property (past_valid && $past(set) && (q == ALL1));

  // Coverage: observe data path taken (q follows d)
  c_data_path:  cover property (past_valid && !$past(set) && (q == $past(d)));

  // Coverage: capture all-zeros via data path
  c_zero:       cover property (past_valid && !$past(set) && ($past(d) == '0) && (q == '0));

  // Coverage: capture a mixed pattern via data path (neither all-0 nor all-1)
  c_mixed:      cover property (past_valid && !$past(set) &&
                                ($past(d) != '0) && ($past(d) != ALL1) &&
                                (q == $past(d)));

  // Coverage: single-cycle set pulse and multi-cycle set stretch
  c_set_pulse:  cover property (set ##1 !set);
  c_set_stretch:cover property (set[*2]);

  // Coverage: q toggles (some bit changes)
  c_q_change:   cover property (past_valid && $changed(q));

endmodule

bind dffs_37 dffs_37_sva u_dffs_37_sva (.clk(clk), .set(set), .d(d), .q(q));