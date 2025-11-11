// SVA checker for HallwayRight
// Focus: correctness of registered color selection, X-safety, operator intent, and branch coverage.

module HallwayRight_sva
(
  input  logic        clk_vga,
  input  logic [9:0]  CurrentX,
  input  logic [8:0]  CurrentY,
  input  logic [7:0]  wall,
  input  logic [7:0]  mapData,
  input  logic [7:0]  mColor
);

  // Track when $past is valid
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk_vga) past_valid <= 1'b1;

  // Known-ness checks to avoid 4-state ambiguity in compares
  // If you expect X/Z on inputs, convert these to assume or disable iff.
  assert property (@(posedge clk_vga) !$isunknown({CurrentX, CurrentY, wall}))
    else $error("HallwayRight: X/Z on inputs");

  // mapData should always mirror mColor
  assert property (@(posedge clk_vga) mapData == mColor)
    else $error("HallwayRight: mapData != mColor");

  // Canonicalized branch conditions (per source, but 2-state simplified)
  wire cond_top    = (CurrentY < 9'd40); // ~(CurrentX<0) is always 1, so this reduces to Y<40
  wire cond_right  = (CurrentX >= 10'd600);
  wire cond_bottom = (CurrentY >= 9'd440) && ((CurrentX < 10'd260) || (CurrentX >= 10'd380));

  // Golden next-state check for mColor (registered one-cycle later)
  // Compare mColor at t+1 to function of inputs at t
  assert property (@(posedge clk_vga)
                   disable iff (!past_valid)
                   mColor == $past( cond_top    ? wall :
                                    cond_right  ? wall :
                                    cond_bottom ? wall :
                                                  8'hB6 ))
    else $error("HallwayRight: mColor next-state mismatch");

  // mColor/mapData should not be X after first cycle
  assert property (@(posedge clk_vga) disable iff(!past_valid) !$isunknown({mColor, mapData}))
    else $error("HallwayRight: X on outputs");

  // Intent/sanity checks for use of bitwise ~ on relational results
  // Guarded by known inputs
  assert property (@(posedge clk_vga) (!$isunknown(CurrentX)) |-> ((~(CurrentX < 10'd600)) == (CurrentX >= 10'd600)))
    else $error("HallwayRight: ~(X<600) not equivalent to X>=600");
  assert property (@(posedge clk_vga) (!$isunknown(CurrentY)) |-> ((~(CurrentY < 9'd440)) == (CurrentY >= 9'd440)))
    else $error("HallwayRight: ~(Y<440) not equivalent to Y>=440");
  assert property (@(posedge clk_vga) (!$isunknown(CurrentX)) |-> !(CurrentX < 0))
    else $error("HallwayRight: (CurrentX<0) should never be true for unsigned");

  // Branch coverage
  cover property (@(posedge clk_vga) cond_top);
  cover property (@(posedge clk_vga) !cond_top && cond_right);
  cover property (@(posedge clk_vga) !cond_top && !cond_right && (CurrentY >= 9'd440) && (CurrentX < 10'd260));
  cover property (@(posedge clk_vga) !cond_top && !cond_right && (CurrentY >= 9'd440) && (CurrentX >= 10'd380));
  cover property (@(posedge clk_vga) !cond_top && !cond_right && (CurrentY < 9'd440) && (CurrentX >= 10'd260) && (CurrentX < 10'd380));

  // Boundary-value coverage
  cover property (@(posedge clk_vga) CurrentY == 9'd39);
  cover property (@(posedge clk_vga) CurrentY == 9'd40);
  cover property (@(posedge clk_vga) CurrentY == 9'd439);
  cover property (@(posedge clk_vga) CurrentY == 9'd440);
  cover property (@(posedge clk_vga) CurrentX == 10'd599);
  cover property (@(posedge clk_vga) CurrentX == 10'd600);
  cover property (@(posedge clk_vga) CurrentX == 10'd259);
  cover property (@(posedge clk_vga) CurrentX == 10'd260);
  cover property (@(posedge clk_vga) CurrentX == 10'd379);
  cover property (@(posedge clk_vga) CurrentX == 10'd380);

endmodule

// Bind into the DUT (accesses internal mColor)
bind HallwayRight HallwayRight_sva hwr_sva (.*);