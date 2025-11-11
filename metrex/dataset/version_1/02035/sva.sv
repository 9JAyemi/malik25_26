Here is a concise SVA package you can bind to the DUT. It checks the full functional mapping and provides focused coverage on each region and key overlaps.

module HallwayRight_sva #(parameter FLOOR = 8'hB6)
(
  input  logic        clk_vga,
  input  logic [9:0]  CurrentX,
  input  logic [8:0]  CurrentY,
  input  logic [7:0]  wall,
  input  logic [7:0]  mapData
);
  // Regions as per DUT intent (simplified)
  wire top_w    = (CurrentY < 40);
  wire right_w  = (CurrentX >= 600);
  wire bottom_w = (CurrentY >= 440) && ((CurrentX < 260) || (CurrentX >= 380));
  wire floor_w  = !(top_w || right_w || bottom_w);

  default clocking cb @(posedge clk_vga); endclocking

  // Functional correctness: mapData must match region mapping
  a_func: assert property (
    mapData == ( (top_w || right_w || bottom_w) ? wall : FLOOR )
  );

  // Output domain check (defensive)
  a_only_vals: assert property ( (mapData == wall) || (mapData == FLOOR) );

  // No X/Z on key signals
  a_no_x: assert property ( !$isunknown({CurrentX, CurrentY, wall, mapData}) );

  // Glitch-free registered output (no change away from posedge)
  a_sync: assert property (@(negedge clk_vga) $stable(mapData));

  // Focused coverage of each branch and key corner cases
  c_top:           cover property ( top_w );
  c_right:         cover property ( !top_w && right_w );
  c_bottom_left:   cover property ( !top_w && !right_w && (CurrentY >= 440) && (CurrentX < 260) );
  c_bottom_right:  cover property ( !top_w && !right_w && (CurrentY >= 440) && (CurrentX >= 380) );
  c_floor:         cover property ( floor_w );
  // Bottom-center gap (floor) coverage
  c_bottom_gap:    cover property ( (CurrentY >= 440) && (CurrentX inside {[260:379]}) && !right_w );
  // Overlap stimulus (top and right true simultaneously)
  c_top_right_ovl: cover property ( top_w && right_w );
endmodule

// Bind example:
// bind HallwayRight HallwayRight_sva sva (.*);