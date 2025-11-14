// SVA checker for SWMaze
// Bind this module to the DUT: bind SWMaze SWMaze_sva sva();

module SWMaze_sva (SWMaze d);

  // Default clock and simple "past valid" guard
  default clocking cb @(posedge d.clk_vga); endclocking
  logic past_valid, past2_valid;
  initial past_valid = 1'b0;
  always @(posedge d.clk_vga) begin
    past_valid  <= 1'b1;
    past2_valid <= past_valid;
  end

  localparam logic [7:0] C_BG = 8'hB6;

  // Geometry predicate for "wall" region (union of all else-if conditions plus the top stripe)
  function automatic bit in_wall (logic [9:0] x, logic [8:0] y);
    if (y < 9'd40)                                                                                     in_wall = 1'b1;
    else if ( (x <= 10'd63)                       && ((y >= 9'd120 && y <= 9'd359) || (y >= 9'd441)) ) in_wall = 1'b1;
    else if ( (x >= 10'd64  && x <= 10'd95 )      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd441)) ) in_wall = 1'b1;
    else if ( (x >= 10'd96  && x <= 10'd127)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280)) ) in_wall = 1'b1;
    else if ( (x >= 10'd128 && x <= 10'd159)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280 && y <= 9'd359)) ) in_wall = 1'b1;
    else if ( (x >= 10'd160 && x <= 10'd191)      && ((y >= 9'd280 && y <= 9'd359) || (y >= 9'd400)) ) in_wall = 1'b1;
    else if ( (x >= 10'd192 && x <= 10'd223)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280 && y <= 9'd359)) ) in_wall = 1'b1;
    else if ( (x >= 10'd224 && x <= 10'd255)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280)) ) in_wall = 1'b1;
    else if ( (x >= 10'd256 && x <= 10'd287)      && ( y >= 9'd120 && y <= 9'd199 ) )                  in_wall = 1'b1;
    else if ( (x >= 10'd288 && x <= 10'd351)      && ( y >= 9'd120 ) )                                 in_wall = 1'b1;
    else if ( (x >= 10'd352 && x <= 10'd383)      && ( y >= 9'd120 && y <= 9'd199 ) )                  in_wall = 1'b1;
    else if ( (x >= 10'd384 && x <= 10'd415)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280)) ) in_wall = 1'b1;
    else if ( (x >= 10'd416 && x <= 10'd447)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280 && y <= 9'd359)) ) in_wall = 1'b1;
    else if ( (x >= 10'd448 && x <= 10'd479)      && ((y >= 9'd280 && y <= 9'd359) || (y >= 9'd400)) ) in_wall = 1'b1;
    else if ( (x >= 10'd480 && x <= 10'd511)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280 && y <= 9'd359)) ) in_wall = 1'b1;
    else if ( (x >= 10'd512 && x <= 10'd543)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd280)) ) in_wall = 1'b1;
    else if ( (x >= 10'd544 && x <= 10'd575)      && ((y >= 9'd120 && y <= 9'd199) || (y >= 9'd441)) ) in_wall = 1'b1;
    else if ( (x >= 10'd576 && x <= 10'd640)      && ((y >= 9'd120 && y <= 9'd359) || (y >= 9'd441)) ) in_wall = 1'b1;
    else                                                                                               in_wall = 1'b0;
  endfunction

  // 1) Map output must mirror internal register
  assert property (d.mapData === d.mColor);

  // 2) Cycle-accurate update: on each clk, mColor equals prior-cycle selection
  assert property (past_valid |-> d.mColor == ( in_wall($past(d.CurrentX), $past(d.CurrentY)) ? $past(d.wall) : C_BG ));

  // 3) Same check also visible at the output
  assert property (past_valid |-> d.mapData == ( in_wall($past(d.CurrentX), $past(d.CurrentY)) ? $past(d.wall) : C_BG ));

  // 4) No X-propagation when prior inputs are known
  assert property (past_valid && !$isunknown($past({d.CurrentX,d.CurrentY,d.wall})) |-> !$isunknown(d.mColor));

  // 5) Stability: if region decision and wall value are unchanged over 2 cycles, mColor is stable
  assert property (past2_valid &&
                   in_wall($past(d.CurrentX)) == in_wall($past($past(d.CurrentX))) &&
                   $past(d.CurrentY)          == $past($past(d.CurrentY)) &&
                   $stable(d.wall)
                   |-> d.mColor == $past(d.mColor));

  // ----------------
  // Functional coverage
  // ----------------

  // Cover both behaviors (wall vs background)
  cover property (past_valid &&  in_wall($past(d.CurrentX),$past(d.CurrentY)) && (d.mColor == $past(d.wall)));
  cover property (past_valid && !in_wall($past(d.CurrentX),$past(d.CurrentY)) && (d.mColor == C_BG));

  // Boundary examples
  cover property (past_valid && ($past(d.CurrentY) == 9'd39) && (d.mColor == $past(d.wall))); // top stripe
  cover property (past_valid && ($past(d.CurrentY) == 9'd40) && !in_wall($past(d.CurrentX),$past(d.CurrentY)) && (d.mColor == C_BG));

  // Representative X-range edges
  cover property (past_valid && ($past(d.CurrentX) == 10'd0)   && ($past(d.CurrentY) == 9'd120) && (d.mColor == $past(d.wall)));
  cover property (past_valid && ($past(d.CurrentX) == 10'd351) && ($past(d.CurrentY) == 9'd200) && (d.mColor == $past(d.wall)));
  cover property (past_valid && ($past(d.CurrentX) == 10'd640) && ($past(d.CurrentY) == 9'd200) && (d.mColor == $past(d.wall)));
  cover property (past_valid && ($past(d.CurrentX) == 10'd641) && ($past(d.CurrentY) == 9'd200) && (d.mColor == C_BG));

endmodule