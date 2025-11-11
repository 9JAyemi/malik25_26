// SVA checker for lvds2lcds
module lvds2lcds_sva #(parameter int divider = 50) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Combinational outputs match intent
  assert property (reset_n == !reset);
  assert property (avs_slave_readdata == shift_busy);
  assert property (scl == (scl_en && div_clk));
  assert property (sld == ((!scl_en && shift_busy) && div_clk));
  assert property (sdi == shift_buffer[6]);

  // Reset behavior (on next clock after reset asserted)
  assert property (reset |=> clk_counter==1 && div_clk==0 && scl_en==0 && shift_busy==0 && shift_counter==0);

  // Idle invariants and write start
  assert property (!shift_busy |=> clk_counter==1 && div_clk==0 && shift_counter==0);
  assert property (!shift_busy && avs_slave_write |=> shift_busy && scl_en && shift_buffer==avs_slave_writedata && clk_counter==1 && div_clk==0 && shift_counter==0);
  assert property (!shift_busy |-> scl==0 && sld==0);

  // Divider counter behavior while busy
  assert property (shift_busy && (clk_counter != (divider/2)) |=> clk_counter == $past(clk_counter)+1 && $stable(div_clk));
  assert property (shift_busy && (clk_counter == (divider/2)) |=> clk_counter==1 && div_clk == !$past(div_clk));

  // Shifting on rising div_clk half-cycle (when old div_clk was 0)
  assert property (shift_busy && (clk_counter==(divider/2)) && (div_clk==0) && scl_en && (shift_counter<6)
                   |=> shift_counter == $past(shift_counter)+1 && shift_buffer == ($past(shift_buffer) << 1));

  // Last bit: stop SCL after 7th shift
  assert property (shift_busy && (clk_counter==(divider/2)) && (div_clk==0) && scl_en && (shift_counter==6)
                   |=> !scl_en);

  // After SCL stopped, next rising half-cycle clears busy
  assert property (shift_busy && (clk_counter==(divider/2)) && (div_clk==0) && !scl_en
                   |=> !shift_busy);

  // Safety/invariants
  assert property (shift_counter <= 6);
  assert property (shift_busy |-> (clk_counter >= 1 && clk_counter <= (divider/2)));
  assert property (!(scl && sld)); // never both high
  assert property (!shift_busy |-> !scl_en); // when idle, SCL must be disabled

  // Read has no side effects
  assert property (avs_slave_read |=> $stable({shift_busy,scl_en,div_clk,shift_counter,shift_buffer,clk_counter}));

  // Simple covers for full transaction and edge cases
  sequence shift_event; shift_busy && (clk_counter==(divider/2)) && (div_clk==0); endsequence
  cover property (!shift_busy ##1 avs_slave_write ##1 shift_busy
                  ##0 shift_event[*7] // 7 data shifts
                  ##1 shift_event     // one more to clear busy
                  ##1 !shift_busy);

  cover property (shift_event && (scl_en==0) && shift_busy); // sld pulse opportunity
  cover property (shift_event && scl_en && (shift_counter==6)); // last-bit event

endmodule

// Bind into DUT (inherits DUT's 'divider' parameter)
bind lvds2lcds lvds2lcds_sva #(.divider(divider)) lvds2lcds_sva_i();