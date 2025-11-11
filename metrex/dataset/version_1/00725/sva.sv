// SVA checker for clk_divider
module clk_divider_sva #(parameter int DIVIDER = 15);

  // Access DUT internals via bind (IN_SIG, OUT_SIG, counter, BITS, MAX, HIGH)

  // Establish a valid past sample
  bit past_valid;
  initial past_valid = 0;
  always @(posedge IN_SIG) past_valid <= 1'b1;

  default clocking cb @(posedge IN_SIG); endclocking
  default disable iff (!past_valid);

  // Parameter/localparam sanity (constant, checked once)
  initial begin
    assert (DIVIDER >= 1) else $error("DIVIDER must be >= 1");
    assert (MAX >= DIVIDER) else $error("MAX must cover DIVIDER");
    if (BITS > 0) assert ((MAX>>1) < DIVIDER) else $error("BITS too small/large for DIVIDER");
  end

  // No X/Z on key signals
  a_no_xz: assert property (!$isunknown({counter, OUT_SIG})));

  // Counter is always within range [0, DIVIDER-1]
  a_range:  assert property (counter < DIVIDER);

  // Modulo-DIVIDER increment behavior
  a_inc:    assert property ( ($past(counter) < DIVIDER-1) |-> counter == $past(counter)+1 );
  a_wrap:   assert property ( ($past(counter) == DIVIDER-1) |-> counter == 0 );

  // OUT matches combinational definition
  a_out_def: assert property (OUT_SIG == (counter <= HIGH));

  // Edge-location and timing properties
  generate
    if (DIVIDER >= 3) begin
      // OUT transitions only at expected counter values
      a_rise_loc: assert property ( $rose(OUT_SIG) |-> counter == 0 );
      a_fall_loc: assert property ( $fell(OUT_SIG) |-> counter == (HIGH+1) );

      // High phase = HIGH+1 cycles, Low phase = DIVIDER-(HIGH+1) cycles
      a_high_len: assert property ( $rose(OUT_SIG) |-> OUT_SIG[* (HIGH+1)] ##1 !OUT_SIG );
      a_low_len:  assert property ( $fell(OUT_SIG) |-> !OUT_SIG[* (DIVIDER-(HIGH+1))] ##1 OUT_SIG );

      // Periodicity: one rising edge every DIVIDER cycles (no earlier rises)
      a_period:   assert property ( $rose(OUT_SIG) |=> (! $rose(OUT_SIG))[* (DIVIDER-1)] ##1 $rose(OUT_SIG) );
    end else begin
      // Degenerate DIVIDER=1 or 2: OUT must be stuck high
      a_stuck_high: assert property (OUT_SIG);
    end
  endgenerate

  // Coverage
  cover_rise: cover property ($rose(OUT_SIG));
  cover_fall: cover property ($fell(OUT_SIG));
  cover_wrap: cover property ( ($past(counter)==DIVIDER-1) ##1 (counter==0) );

  // Cover all counter states reached
  genvar i;
  generate
    for (i = 0; i < DIVIDER; i++) begin : cov_states
      cover property (counter == i);
    end
  endgenerate

endmodule

// Bind checker into all clk_divider instances
bind clk_divider clk_divider_sva #(.DIVIDER(DIVIDER)) clk_divider_sva_i();