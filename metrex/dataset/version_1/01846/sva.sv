// SVA for vga_sync_generator
// Bind this file to the DUT: bind vga_sync_generator vga_sync_generator_sva sva();

module vga_sync_generator_sva;
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X-state sanitation once we have at least 1 past sample
  assert property (past_valid |-> !$isunknown({vga_h_sync, vga_v_sync, inDisplayArea, CounterX, CounterY}));

  // CounterX progression and bounds
  assert property (CounterX <= COUNT_DOTS);
  assert property (disable iff (!past_valid)
                   ($past(CounterX) == COUNT_DOTS) |-> (CounterX == 0));
  assert property (disable iff (!past_valid)
                   ($past(CounterX) <  COUNT_DOTS) |-> (CounterX == $past(CounterX) + 1));

  // CounterY progression and bounds
  assert property (CounterY <= COUNT_LINES);
  // Y holds while X advances (no wrap)
  assert property (disable iff (!past_valid)
                   ($past(CounterX) != COUNT_DOTS) |-> (CounterY == $past(CounterY)));
  // Y increments on X wrap unless Y maxed, then wraps to 0
  assert property (disable iff (!past_valid)
                   ($past(CounterX) == COUNT_DOTS && $past(CounterY) <  COUNT_LINES) |-> (CounterY == $past(CounterY) + 1));
  assert property (disable iff (!past_valid)
                   ($past(CounterX) == COUNT_DOTS && $past(CounterY) == COUNT_LINES) |-> (CounterY == 0));

  // inDisplayArea must exactly reflect visible region (combinational to current counters)
  assert property (inDisplayArea == ((CounterX < WIDTH) && (CounterY < HEIGHT)));

  // HS mapping (registered from previous X)
  assert property (disable iff (!past_valid)
    vga_h_sync == (($past(CounterX) >= (WIDTH + H_FRONT_PORCH)) &&
                   ($past(CounterX) <  (WIDTH + H_FRONT_PORCH + H_SYNC_PULSE)))
  );

  // VS mapping (registered from previous Y)
  assert property (disable iff (!past_valid)
    vga_v_sync == (($past(CounterY) >= (HEIGHT + V_FRONT_PORCH)) &&
                   ($past(CounterY) <  (HEIGHT + V_FRONT_PORCH + V_SYNC_PULSE)))
  );

  // HS pulse width and edge alignment (in pixel clocks)
  assert property (disable iff (!past_valid)
    $rose(vga_h_sync) |-> ($past(CounterX) == (WIDTH + H_FRONT_PORCH)) &&
                        (vga_h_sync[*H_SYNC_PULSE] ##1 !vga_h_sync)
  );
  assert property (disable iff (!past_valid)
    $fell(vga_h_sync) |-> ($past(CounterX) == (WIDTH + H_FRONT_PORCH + H_SYNC_PULSE - 1))
  );

  // VS edge alignment to Y thresholds (width is in lines, mapping assertion above suffices)
  assert property (disable iff (!past_valid)
    $rose(vga_v_sync) |-> ($past(CounterY) == (HEIGHT + V_FRONT_PORCH))
  );
  assert property (disable iff (!past_valid)
    $fell(vga_v_sync) |-> ($past(CounterY) == (HEIGHT + V_FRONT_PORCH + V_SYNC_PULSE - 1))
  );

  // Coverage
  cover property (past_valid && $rose(vga_h_sync));                // HS pulse seen
  cover property (past_valid && $rose(vga_v_sync));                // VS pulse seen
  cover property (past_valid && ($past(CounterX)==COUNT_DOTS && CounterX==0)); // X wrap
  cover property (past_valid && ($past(CounterX)==COUNT_DOTS && $past(CounterY)==COUNT_LINES && CounterY==0)); // Frame wrap
  cover property (past_valid && inDisplayArea);                    // Visible pixel
  cover property (past_valid && !inDisplayArea);                   // Non-visible pixel
endmodule

bind vga_sync_generator vga_sync_generator_sva sva();