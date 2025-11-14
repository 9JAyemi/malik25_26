// SVA for VGA_DRIVER
// Bind this module to the DUT (bind statement at bottom)

module vga_driver_sva
  #(parameter int TOTAL_W   = `TOTAL_SCREEN_WIDTH,
              int TOTAL_H   = `TOTAL_SCREEN_HEIGHT,
              int VISIBLE_W = `VISIBLE_SCREEN_WIDTH,
              int VISIBLE_H = `VISIBLE_SCREEN_HEIGHT,
              int HSYNC_S   = 656,
              int HSYNC_E   = 752,
              int VSYNC_S   = 490,
              int VSYNC_E   = 492)
(
  input logic        CLOCK,
  input logic        RESET,
  input logic [7:0]  PIXEL_COLOR_IN,
  input logic [9:0]  PIXEL_X,
  input logic [9:0]  PIXEL_Y,
  input logic [7:0]  PIXEL_COLOR_OUT,
  input logic        H_SYNC_NEG,
  input logic        V_SYNC_NEG,
  // internal regs
  input logic [9:0]  pixel_count,
  input logic [9:0]  line_count
);

  // Basic sanity
  assert property (@(posedge CLOCK) !$isunknown({pixel_count,line_count,PIXEL_X,PIXEL_Y,H_SYNC_NEG,V_SYNC_NEG,PIXEL_COLOR_OUT}));

  // Reset behavior (synchronous)
  assert property (@(posedge CLOCK) RESET |=> (pixel_count==0 && line_count==0));
  assert property (@(posedge CLOCK) RESET && $past(RESET) |-> (pixel_count==0 && line_count==0));

  // Range constraints
  assert property (@(posedge CLOCK) disable iff (RESET) pixel_count < TOTAL_W);
  assert property (@(posedge CLOCK) disable iff (RESET) line_count  < TOTAL_H);

  // Pixel counter increments and wraps
  assert property (@(posedge CLOCK) disable iff (RESET)
                   ($past(pixel_count,1,RESET) != TOTAL_W-1) |-> pixel_count == $past(pixel_count,1,RESET)+1);
  assert property (@(posedge CLOCK) disable iff (RESET)
                   ($past(pixel_count,1,RESET) == TOTAL_W-1) |-> pixel_count == 0);

  // Line counter holds/increments/ wraps at end-of-line and end-of-frame
  assert property (@(posedge CLOCK) disable iff (RESET)
                   ($past(pixel_count,1,RESET) != TOTAL_W-1) |-> line_count == $past(line_count,1,RESET));
  assert property (@(posedge CLOCK) disable iff (RESET)
                   ($past(pixel_count,1,RESET) == TOTAL_W-1 && $past(line_count,1,RESET) != TOTAL_H-1)
                   |-> line_count == $past(line_count,1,RESET)+1);
  assert property (@(posedge CLOCK) disable iff (RESET)
                   ($past(pixel_count,1,RESET) == TOTAL_W-1 && $past(line_count,1,RESET) == TOTAL_H-1)
                   |-> line_count == 0);

  // Output mapping to internal state
  assert property (@(posedge CLOCK) PIXEL_X == pixel_count);
  assert property (@(posedge CLOCK) PIXEL_Y == line_count);

  // Color gating
  assert property (@(posedge CLOCK)
                   PIXEL_COLOR_OUT == ((pixel_count < VISIBLE_W) ? PIXEL_COLOR_IN : 8'h00));

  // Sync generation exact conditions
  assert property (@(posedge CLOCK) disable iff (RESET)
                   H_SYNC_NEG == ~((pixel_count >= HSYNC_S) && (pixel_count < HSYNC_E)));
  assert property (@(posedge CLOCK) disable iff (RESET)
                   V_SYNC_NEG == ~((line_count  >= VSYNC_S) && (line_count  < VSYNC_E)));

  // Sync edge checks (redundant but precise edge validation)
  assert property (@(posedge CLOCK) disable iff (RESET)
                   $past(pixel_count,1,RESET) == HSYNC_S-1 |-> H_SYNC_NEG == 1'b0);
  assert property (@(posedge CLOCK) disable iff (RESET)
                   $past(pixel_count,1,RESET) == HSYNC_E-1 |-> H_SYNC_NEG == 1'b1);
  assert property (@(posedge CLOCK) disable iff (RESET)
                   $past(line_count,1,RESET) == VSYNC_S-1 |-> V_SYNC_NEG == 1'b0);
  assert property (@(posedge CLOCK) disable iff (RESET)
                   $past(line_count,1,RESET) == VSYNC_E-1 |-> V_SYNC_NEG == 1'b1);

  // Functional coverage
  cover property (@(posedge CLOCK) disable iff (RESET)
                  pixel_count==TOTAL_W-1 ##1 pixel_count==0);                           // H wrap
  cover property (@(posedge CLOCK) disable iff (RESET)
                  line_count==TOTAL_H-1 && pixel_count==TOTAL_W-1 ##1
                  line_count==0 && pixel_count==0);                                     // Frame wrap
  cover property (@(posedge CLOCK) disable iff (RESET)
                  pixel_count==VISIBLE_W-1 ##1 pixel_count==VISIBLE_W &&
                  (PIXEL_COLOR_OUT==8'h00));                                            // Visible->blank boundary
  cover property (@(posedge CLOCK) disable iff (RESET)
                  pixel_count==HSYNC_S ##[1:200] pixel_count==HSYNC_E);                 // HSYNC pulse seen
  cover property (@(posedge CLOCK) disable iff (RESET)
                  line_count==VSYNC_S  ##[1:10]  line_count==VSYNC_E);                  // VSYNC pulse seen
  cover property (@(posedge CLOCK) disable iff (RESET)
                  (pixel_count< VISIBLE_W) && (PIXEL_COLOR_OUT==PIXEL_COLOR_IN));       // Pass-through color
  cover property (@(posedge CLOCK) disable iff (RESET)
                  (pixel_count>=VISIBLE_W) && (PIXEL_COLOR_OUT==8'h00));                // Blanked color

endmodule

// Bind to the DUT
bind VGA_DRIVER vga_driver_sva #(
  .TOTAL_W(`TOTAL_SCREEN_WIDTH),
  .TOTAL_H(`TOTAL_SCREEN_HEIGHT),
  .VISIBLE_W(`VISIBLE_SCREEN_WIDTH),
  .VISIBLE_H(`VISIBLE_SCREEN_HEIGHT)
) vga_driver_sva_i (.*);