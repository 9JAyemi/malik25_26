// SVA for vga_renderer
// Bind inside DUT scope to access internals
module vga_renderer_sva;
  default clocking @(posedge vga_clk); endclocking
  default disable iff (!reset_n);

  localparam int H_SYNC_START = WIDTH + H_FRONT_PORCH;
  localparam int H_SYNC_END   = WIDTH + H_FRONT_PORCH + H_SYNC;
  localparam int V_SYNC_START = HEIGHT + V_FRONT_PORCH;
  localparam int V_SYNC_END   = HEIGHT + V_FRONT_PORCH + V_SYNC;

  // Reset behavior (checked even while in reset)
  assert property (@(posedge vga_clk) disable iff (1'b0)
                   (!reset_n |-> (x_pos==0 && y_pos==0 && hsync==0 && vsync==0)));

  // Position ranges
  assert property (x_pos < PIXELS_PER_LINE);
  assert property (y_pos < LINES_PER_FRAME);

  // x counter behavior
  assert property (!x_max |=> x_pos == $past(x_pos)+1);
  assert property ( x_max |=> x_pos == 0);

  // y counter behavior
  assert property (!x_max |=> y_pos == $past(y_pos));
  assert property ( x_max && !y_max |=> y_pos == $past(y_pos)+1);
  assert property ( x_max &&  y_max |=> y_pos == 0);

  // x_max/y_max consistency
  assert property (x_max == (x_pos == PIXELS_PER_LINE-1));
  assert property (y_max == (y_pos == LINES_PER_FRAME-1));

  // HSYNC/VSYNC polarity
  assert property (vga_hsync == ~hsync);
  assert property (vga_vsync == ~vsync);

  // HSYNC timing within a line
  assert property ((x_pos >= H_SYNC_START && x_pos < H_SYNC_END) |-> vga_hsync == 1'b0);
  assert property ((x_pos <  H_SYNC_START || x_pos >= H_SYNC_END) |-> vga_hsync == 1'b1);
  assert property ((x_pos == H_SYNC_START) |-> vga_hsync == 1'b0);
  assert property ((x_pos == H_SYNC_END)   |-> vga_hsync == 1'b1);

  // VSYNC timing across lines
  assert property ((y_pos >= V_SYNC_START && y_pos < V_SYNC_END) |-> vga_vsync == 1'b0);
  assert property ((y_pos <  V_SYNC_START || y_pos >= V_SYNC_END) |-> vga_vsync == 1'b1);
  assert property ((x_pos==0 && y_pos == V_SYNC_START) |-> vga_vsync == 1'b0);
  assert property ((x_pos==0 && y_pos == V_SYNC_END)   |-> vga_vsync == 1'b1);

  // Blanking flags
  assert property (fb_hblank == (x_pos >= WIDTH));
  assert property (fb_vblank == (y_pos >= HEIGHT));

  // RGB gating
  assert property (((x_pos < WIDTH) && (y_pos < HEIGHT)) |-> (vga_red==red && vga_green==green && vga_blue==blue));
  assert property (((x_pos >= WIDTH) || (y_pos >= HEIGHT)) |-> (vga_red==8'h00 && vga_green==8'h00 && vga_blue==8'h00));

  // Coverage
  cover property (disable iff (1'b0) $rose(reset_n));
  cover property (x_pos==0 && y_pos==0);
  cover property (x_pos==H_SYNC_START && vga_hsync==1'b0);
  cover property (x_pos==H_SYNC_END   && vga_hsync==1'b1);
  cover property (x_pos==0 && y_pos==V_SYNC_START && vga_vsync==1'b0);
  cover property (x_pos==0 && y_pos==V_SYNC_END   && vga_vsync==1'b1);
  cover property (x_pos==WIDTH-1 && y_pos==HEIGHT-1);
  cover property (x_max && y_max ##1 (x_pos==0 && y_pos==0));
endmodule

bind vga_renderer vga_renderer_sva sva_inst();