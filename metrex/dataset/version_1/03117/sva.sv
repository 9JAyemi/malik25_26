// SVA for barrel_shifter
module barrel_shifter_sva (
  input logic         clk,
  input logic         reset,
  input logic [15:0]  data,
  input logic [3:0]   shift_amount,
  input logic         load,
  input logic         ena,
  input logic [15:0]  q
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Knownness
  a_q_known:                assert property (!$isunknown(q));
  a_ctrls_known_when_ena:   assert property (ena && !load |-> !$isunknown(shift_amount));

  // Reset behavior (async and sync)
  a_async_reset_clears:     assert property (@(posedge reset) q == 16'h0000);
  a_sync_reset_clears:      assert property (reset |-> q == 16'h0000);

  // Load has priority and correctness
  a_load_sets_q:            assert property (load |-> q == data);

  // Hold when idle
  a_hold_idle:              assert property (!load && !ena |-> q == $past(q));

  // Hold when shift_amount == 0 (ena but no shift)
  a_hold_zero_shift:        assert property (ena && !load && (shift_amount == 4'd0) |-> q == $past(q));

  // Shift-left by 1..15 with zero fill
  a_shift_value:            assert property (ena && !load && (shift_amount inside {[4'd1:4'd15]})
                                             |-> q == ($past(q) << shift_amount));

  a_zero_fill_low_bits:     assert property (ena && !load && (shift_amount inside {[4'd1:4'd15]})
                                             |-> (q & ((16'h1 << shift_amount) - 16'h1)) == 16'h0000);

  // No unintended update beyond load/ena paths
  a_only_updates_when_expected:
                             assert property (!(load || ena) |-> q == $past(q));

  // Coverage
  c_reset:                  cover property (@(posedge reset) 1);
  c_load:                   cover property (load && !reset);
  c_shift_any:              cover property (ena && !load && (shift_amount inside {[4'd1:4'd15]}));
  c_shift1:                 cover property (ena && !load && shift_amount == 4'd1);
  c_shift8:                 cover property (ena && !load && shift_amount == 4'd8);
  c_shift15:                cover property (ena && !load && shift_amount == 4'd15);
  c_zero_shift:             cover property (ena && !load && shift_amount == 4'd0);
  c_load_and_ena:           cover property (load && ena);
  c_drop_msb_when_shift:    cover property (ena && !load && (shift_amount inside {[4'd1:4'd15]}) && $past(q[15]));

endmodule

// Bind into DUT
bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (
  .clk(clk), .reset(reset), .data(data), .shift_amount(shift_amount),
  .load(load), .ena(ena), .q(q)
);