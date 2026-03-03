// SVA for global_reset
module global_reset_sva #(
  parameter int WIDTH = 8
)(
  input  logic               clock_i,
  input  logic               forced_reset_i,
  input  logic               n_reset_o,
  input  logic               n_limited_reset_o,
  input  logic [WIDTH-1:0]   reset_counter
);

  default clocking cb @(negedge clock_i); endclocking

  // Basic sanity
  a_known:        assert property ( !$isunknown({forced_reset_i, n_reset_o, n_limited_reset_o, reset_counter}) );
  a_init_val:     assert property ( $initstate |-> reset_counter == WIDTH'(8'd1) );

  // Output logic equivalence
  a_lim_eq:       assert property ( n_limited_reset_o == (reset_counter <= WIDTH'(8'd1)) );
  a_full_eq:      assert property ( n_reset_o        == ((reset_counter <= WIDTH'(8'd1)) & !forced_reset_i) );

  // Forced reset gating behavior
  a_force_low:    assert property ( forced_reset_i  |-> (n_reset_o == 1'b0) );
  a_force_match:  assert property ( !forced_reset_i |-> (n_reset_o == n_limited_reset_o) );

  // Counter behavior
  a_inc_when_nz:  assert property ( (reset_counter != WIDTH'(8'd0)) |=> reset_counter == $past(reset_counter) + WIDTH'(8'd1) );
  a_hold_at_zero: assert property ( (reset_counter == WIDTH'(8'd0)) |=> reset_counter == WIDTH'(8'd0) );

  // Outputs in terminal (stuck-at-zero) phase
  a_zero_phase:   assert property ( (reset_counter == WIDTH'(8'd0)) |-> ( n_limited_reset_o && (n_reset_o == !forced_reset_i) ) );

  // Coverage
  c_boot_drop:    cover property ( reset_counter == WIDTH'(8'd1) ##1 (reset_counter == WIDTH'(8'd2) && !n_limited_reset_o) );
  c_wrap:         cover property ( reset_counter == WIDTH'(8'hFF) ##1 reset_counter == WIDTH'(8'h00) );
  c_force_hi_win: cover property ( (reset_counter <= WIDTH'(8'd1)) && forced_reset_i );
  c_force_hi_run: cover property ( (reset_counter  > WIDTH'(8'd1)) && forced_reset_i );
  c_force_toggle: cover property ( $rose(forced_reset_i) ); 
  c_force_untgl:  cover property ( $fell(forced_reset_i) );

endmodule

// Bind into DUT
bind global_reset global_reset_sva u_global_reset_sva (
  .clock_i           (clock_i),
  .forced_reset_i    (forced_reset_i),
  .n_reset_o         (n_reset_o),
  .n_limited_reset_o (n_limited_reset_o),
  .reset_counter     (reset_counter)
);