// SVA for VGACtrl
// Bind or instantiate this module alongside the DUT
module VGACtrl_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic [9:0]  CounterX,
  input  logic [9:0]  CounterY,
  input  logic        inDisplayArea,
  input  logic        vga_h_sync,
  input  logic        vga_v_sync
);

  // Parameters derived from DUT
  localparam int H_MAX  = 10'h320; // 800-1
  localparam int V_MAX  = 10'h209; // 521
  localparam int H_VIS  = 640;
  localparam int V_VIS  = 480;
  localparam int HS_BEG = 656;
  localparam int HS_END = 752;     // exclusive upper bound for vga_HS true
  localparam int VS0    = 490;
  localparam int VS1    = 491;

  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  // Safe $past guard
  logic past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // CounterX: range and step/wrap
  assert property (CounterX <= H_MAX);
  assert property (past_valid |-> ($past(CounterX)==H_MAX ? (CounterX==0)
                                                         : (CounterX==$past(CounterX)+1)));

  // CounterY: range and step/wrap, only at end of line
  assert property (CounterY <= V_MAX);
  assert property (past_valid |-> ($past(CounterX)==H_MAX
                                   ? ($past(CounterY)==V_MAX ? (CounterY==0)
                                                             : (CounterY==$past(CounterY)+1))
                                   : (CounterY==$past(CounterY))));
  assert property (past_valid && (CounterY != $past(CounterY)) |-> $past(CounterX)==H_MAX);

  // Functional correctness of outputs
  assert property (vga_h_sync == ~((CounterX > (HS_BEG-1)) && (CounterX < HS_END)));
  assert property (vga_v_sync == ~((CounterY == VS0) || (CounterY == VS1)));
  assert property (inDisplayArea == ((CounterX < H_VIS) && (CounterY < V_VIS)));

  // In-display implies syncs are inactive (high)
  assert property (inDisplayArea |-> (vga_h_sync && vga_v_sync));

  // Reset effect on next clock (avoid default disable for this one)
  assert property (@(posedge clk) disable iff (1'b0)
                   $rose(reset) |-> (CounterX==0 && CounterY==0 && inDisplayArea==0));

  // ------------- Coverage -------------
  // Line wrap and frame wrap
  cover property (past_valid && $past(CounterX)==H_MAX && CounterX==0);
  cover property (past_valid && $past(CounterX)==H_MAX && $past(CounterY)==V_MAX && CounterY==0);

  // Enter/exit visible area
  cover property (past_valid && !$past(inDisplayArea) && inDisplayArea);
  cover property (past_valid &&  $past(inDisplayArea) && !inDisplayArea);

  // HSync boundary behavior within a line
  cover property (CounterX==655 && vga_h_sync==1 ##1
                  CounterX==656 && vga_h_sync==0 ##1
                  CounterX==751 && vga_h_sync==0 ##1
                  CounterX==752 && vga_h_sync==1);

  // VSync low lines observed
  cover property (CounterY==VS0 && vga_v_sync==0);
  cover property (CounterY==VS1 && vga_v_sync==0);

  // Visible-area edge pixels
  cover property (CounterX==H_VIS-1 && CounterY==V_VIS-1 && inDisplayArea && vga_h_sync && vga_v_sync);
  cover property (CounterX==H_VIS && CounterY==V_VIS-1 && !inDisplayArea);
  cover property (CounterX==H_VIS-1 && CounterY==V_VIS && !inDisplayArea);

endmodule

// Bind example:
// bind VGACtrl VGACtrl_sva u_VGACtrl_sva(.clk(clk), .reset(reset),
//   .CounterX(CounterX), .CounterY(CounterY),
//   .inDisplayArea(inDisplayArea), .vga_h_sync(vga_h_sync), .vga_v_sync(vga_v_sync));