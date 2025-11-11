// SVA checker for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        load,
  input logic        up_down,
  input logic [2:0]  load_val,
  input logic [2:0]  count
);

  // track that we have one cycle of history for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Inputs/output must be known when not in reset
  a_inputs_known:  assert property (disable iff (reset || !past_valid)
                                   !$isunknown({load, up_down, load_val}));
  a_output_known:  assert property (disable iff (reset || !past_valid)
                                   !$isunknown(count));

  // Synchronous reset to zero (dominates all)
  a_sync_reset:    assert property (reset |=> count == 3'd0);

  // Load has priority over up/down when not in reset
  a_load:          assert property (disable iff (reset || !past_valid)
                                   load |=> count == $past(load_val));

  // Count up/down when not loading and not in reset (3-bit modulo arithmetic)
  a_inc:           assert property (disable iff (reset || !past_valid)
                                   (!load && up_down) |=> count == $past(count) + 3'd1);
  a_dec:           assert property (disable iff (reset || !past_valid)
                                   (!load && !up_down) |=> count == $past(count) - 3'd1);

  // Coverage
  c_reset:         cover  property (reset);
  c_load_any:      cover  property (!reset && load);
  c_load_min:      cover  property (!reset && load && load_val == 3'd0);
  c_load_max:      cover  property (!reset && load && load_val == 3'd7);
  c_inc_any:       cover  property (disable iff (reset || !past_valid)
                                   (!load && up_down) |=> count == $past(count) + 3'd1);
  c_dec_any:       cover  property (disable iff (reset || !past_valid)
                                   (!load && !up_down) |=> count == $past(count) - 3'd1);
  c_wrap_up:       cover  property (disable iff (reset || !past_valid)
                                   (!load && up_down && $past(count) == 3'd7) |=> count == 3'd0);
  c_wrap_down:     cover  property (disable iff (reset || !past_valid)
                                   (!load && !up_down && $past(count) == 3'd0) |=> count == 3'd7);

endmodule

// Bind into the DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva (.*);