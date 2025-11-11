// Bind this SVA to the DUT
bind center_pos center_pos_sva u_center_pos_sva();

module center_pos_sva;

  // In bound context, we can directly see DUT signals
  localparam logic [31:0] T = 32'h0007_5300;

  default clocking cb @(posedge clk); endclocking

  // ----------------------------
  // Reset behavior
  // ----------------------------
  assert property (cb) reset |=> (center_x==16'h0 && center_y==16'h0 &&
                                  center_x_temp==32'h0 && center_y_temp==32'h0 &&
                                  pixel_counter==32'h0 && dirty==32'h0);

  // ----------------------------
  // Index sanity and X-safety
  // ----------------------------
  // Index used on 'valid' is always within [0:15] while accumulating
  assert property (cb) disable iff (reset)
    (dirty < T) |-> (dirty[31:16] <= 16'd15);

  // The valid bit used is known (no X) when consulted
  assert property (cb) disable iff (reset)
    (dirty < T) |-> !$isunknown(valid[dirty[31:16]]);

  // Data used when valid must be known
  assert property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b1) |-> !$isunknown({x_row,y_col});

  // ----------------------------
  // Dirty counter behavior
  // ----------------------------
  // While accumulating, dirty increments by exactly 1 each cycle
  assert property (cb) disable iff (reset)
    (dirty < T) |=> (dirty == $past(dirty) + 32'd1);

  // Commit happens exactly when previous dirty reached threshold
  assert property (cb) disable iff (reset)
    (dirty >= T) |-> ($past(dirty) == T);

  // After commit, internal accumulators and counters clear
  assert property (cb) disable iff (reset)
    (dirty >= T) |=> (center_x_temp==32'h0 && center_y_temp==32'h0 &&
                      pixel_counter==32'h0 && dirty==32'h0);

  // ----------------------------
  // Accumulation behavior
  // ----------------------------
  // On a valid hit, the sums and pixel_counter increment appropriately
  assert property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b1) |=> (
      center_x_temp == $past(center_x_temp) + $past(x_row) &&
      center_y_temp == $past(center_y_temp) + $past(y_col) &&
      pixel_counter  == $past(pixel_counter) + 32'd1
    );

  // On an invalid step, sums and pixel_counter hold
  assert property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b0) |=> (
      center_x_temp == $past(center_x_temp) &&
      center_y_temp == $past(center_y_temp) &&
      pixel_counter  == $past(pixel_counter)
    );

  // Optional overflow detection: sums should not wrap (monotonic non-decreasing on valid)
  assert property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b1) |=> (
      center_x_temp >= $past(center_x_temp) && center_y_temp >= $past(center_y_temp)
    );

  // Pixel count cannot exceed total steps since last clear
  assert property (cb) disable iff (reset)
    (pixel_counter <= dirty);

  // ----------------------------
  // Output update and division safety
  // ----------------------------
  // No divide-by-zero when committing results
  assert property (cb) disable iff (reset)
    (dirty >= T) |-> ($past(pixel_counter) != 32'd0);

  // Outputs only change on commit (or reset)
  assert property (cb) disable iff (reset)
    (dirty < T) |=> ($stable(center_x) && $stable(center_y));

  // Committed outputs equal truncated division of accumulated sums
  assert property (cb) disable iff (reset)
    (dirty >= T && $past(pixel_counter) != 32'd0) |-> (
      center_x == ( ($past(center_x_temp) / $past(pixel_counter)) )[15:0] &&
      center_y == ( ($past(center_y_temp) / $past(pixel_counter)) )[15:0]
    );

  // ----------------------------
  // Coverage
  // ----------------------------
  // See both branches and a commit with non-zero pixel count
  cover property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b1);

  cover property (cb) disable iff (reset)
    (dirty < T && valid[dirty[31:16]] === 1'b0);

  cover property (cb) disable iff (reset)
    (dirty >= T && $past(pixel_counter) > 0);

  // Exercise multiple valid index values
  cover property (cb) disable iff (reset)
    (dirty[31:16] == 16'd0) ##1 (dirty[31:16] == 16'd1) ##1 (dirty[31:16] == 16'd2) ##1
    (dirty[31:16] == 16'd3) ##1 (dirty[31:16] == 16'd4);

endmodule