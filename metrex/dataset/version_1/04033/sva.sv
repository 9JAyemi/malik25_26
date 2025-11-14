// SVA for vga_sync
// Bind these assertions to the DUT

module vga_sync_sva #(
  // Mirror DUT constants (keep in sync with DUT)
  parameter int H_FRONT = 56,
  parameter int H_SYNC  = 120,
  parameter int H_BACK  = 64,
  parameter int H_ACT   = 800,
  parameter int H_TOTAL = H_FRONT+H_SYNC+H_BACK+H_ACT,
  parameter int H_BLANK = H_FRONT+H_SYNC+H_BACK,
  parameter int H_TOTAL_WIDTH = 10,

  parameter int V_FRONT = 37,
  parameter int V_SYNC  = 6,
  parameter int V_BACK  = 23,
  parameter int V_ACT   = 600,
  parameter int V_TOTAL = V_FRONT+V_SYNC+V_BACK+V_ACT,
  parameter int V_BLANK = V_FRONT+V_SYNC+V_BACK,
  parameter int V_TOTAL_WIDTH = 10
)(
  input  logic                       clock,
  input  logic                       aresetn,
  input  logic [2:0]                 color,
  input  logic                       vga_clk,
  input  logic [7:0]                 R, G, B,
  input  logic                       h_sync,
  input  logic                       v_sync,
  input  logic                       blank_n,
  input  logic                       sync_n,
  // internal DUT state
  input  logic [H_TOTAL_WIDTH-1:0]   hor_pos,
  input  logic [V_TOTAL_WIDTH-1:0]   ver_pos
);

  // vga_clk must be exact inversion of clock
  assert property (@(posedge clock) vga_clk == ~clock);
  assert property (@(negedge clock) vga_clk == ~clock);

  // Reset behavior (clock domain)
  assert property (@(posedge clock) !aresetn |-> (hor_pos==0 && h_sync==0 && R==0 && G==0 && B==0));

  // hor_pos range and stepping
  assert property (@(posedge clock) disable iff (!aresetn) hor_pos <= H_TOTAL);
  assert property (@(posedge clock) disable iff (!aresetn)
                   $past(hor_pos) < H_TOTAL |-> hor_pos == $past(hor_pos)+1);
  assert property (@(posedge clock) disable iff (!aresetn)
                   $past(hor_pos) == H_TOTAL |-> hor_pos == '0);

  // h_sync edges occur at precise horizontal positions
  assert property (@(posedge clock) disable iff (!aresetn) $rose(h_sync) |-> $past(hor_pos) == (H_FRONT-1));
  assert property (@(posedge clock) disable iff (!aresetn) $fell(h_sync) |-> $past(hor_pos) == (H_FRONT+H_SYNC-1));

  // h_sync level matches position window
  assert property (@(posedge clock) disable iff (!aresetn)
                   h_sync == (hor_pos >= H_FRONT && hor_pos <= (H_FRONT+H_SYNC-1)));

  // ver_pos range and stepping on h_sync domain
  assert property (@(posedge h_sync) disable iff (!aresetn) ver_pos <= V_TOTAL);
  assert property (@(posedge h_sync) disable iff (!aresetn)
                   $past(ver_pos) < V_TOTAL |-> ver_pos == $past(ver_pos)+1);
  assert property (@(posedge h_sync) disable iff (!aresetn)
                   $past(ver_pos) == V_TOTAL |-> ver_pos == '0);

  // v_sync edges occur at precise vertical positions (on h_sync clock)
  assert property (@(posedge h_sync) disable iff (!aresetn) $rose(v_sync) |-> $past(ver_pos) == (V_FRONT-1));
  assert property (@(posedge h_sync) disable iff (!aresetn) $fell(v_sync) |-> $past(ver_pos) == (V_FRONT+V_SYNC-1));

  // v_sync level matches position window (check on h_sync domain)
  assert property (@(posedge h_sync) disable iff (!aresetn)
                   v_sync == (ver_pos >= V_FRONT && ver_pos <= (V_FRONT+V_SYNC-1)));

  // Blanking expression correctness
  assert property (@(posedge clock)
                   blank_n == ~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)));

  // RGB must be black during blanking
  assert property (@(posedge clock) disable iff (!aresetn)
                   ((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) |-> (R==0 && G==0 && B==0));

  // Active area color generation: solid colors
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && color==3'b110)
                   |-> (R==8'd255 && G==8'd0 && B==8'd0));
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && color==3'b101)
                   |-> (R==8'd0 && G==8'd255 && B==8'd0));
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && color==3'b011)
                   |-> (R==8'd0 && G==8'd0 && B==8'd255));

  // Active area color generation: gradient (R and B from previous hor_pos; G from ver_pos when no h_sync edge)
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && color==3'b100)
                   |-> (R==$past(hor_pos[7:0]) && B==$past(hor_pos[7:0])));
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && color==3'b100 && !$rose(h_sync))
                   |-> (G==ver_pos[7:0]));

  // Active area: unspecified colors hold previous RGB
  assert property (@(posedge clock) disable iff (!aresetn)
                   (~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) &&
                    !(color inside {3'b100,3'b110,3'b101,3'b011}))
                   |-> $stable({R,G,B}));

  // sync_n is constant high
  assert property (@(posedge clock) sync_n == 1'b1);

  // No X on primary outputs when not in reset
  assert property (@(posedge clock) disable iff (!aresetn)
                   !$isunknown({R,G,B,h_sync,v_sync,blank_n,sync_n,vga_clk}));

  // ---------------- Coverage ----------------
  // Horizontal line wrap
  cover property (@(posedge clock) disable iff (!aresetn) (hor_pos==H_TOTAL) ##1 (hor_pos==0));
  // Vertical frame wrap
  cover property (@(posedge h_sync) disable iff (!aresetn) (ver_pos==V_TOTAL) ##1 (ver_pos==0));
  // h_sync and v_sync pulses
  cover property (@(posedge clock) disable iff (!aresetn) $rose(h_sync));
  cover property (@(posedge h_sync) disable iff (!aresetn) $rose(v_sync));
  // Blanking enter/exit
  cover property (@(posedge clock) $fell(blank_n));
  cover property (@(posedge clock) $rose(blank_n));
  // Color modes exercised in active region
  cover property (@(posedge clock) disable iff (!aresetn)
                  ~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && (color==3'b110));
  cover property (@(posedge clock) disable iff (!aresetn)
                  ~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && (color==3'b101));
  cover property (@(posedge clock) disable iff (!aresetn)
                  ~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && (color==3'b011));
  cover property (@(posedge clock) disable iff (!aresetn)
                  ~((hor_pos < H_BLANK) || (ver_pos < V_BLANK)) && (color==3'b100));

endmodule

// Bind to DUT (adjust instance path if needed)
bind vga_sync vga_sync_sva #(
  .H_FRONT(56), .H_SYNC(120), .H_BACK(64), .H_ACT(800),
  .H_TOTAL(56+120+64+800), .H_BLANK(56+120+64), .H_TOTAL_WIDTH(10),
  .V_FRONT(37), .V_SYNC(6), .V_BACK(23), .V_ACT(600),
  .V_TOTAL(37+6+23+600), .V_BLANK(37+6+23), .V_TOTAL_WIDTH(10)
) vga_sync_sva_i (
  .clock(clock),
  .aresetn(aresetn),
  .color(color),
  .vga_clk(vga_clk),
  .R(R), .G(G), .B(B),
  .h_sync(h_sync),
  .v_sync(v_sync),
  .blank_n(blank_n),
  .sync_n(sync_n),
  .hor_pos(hor_pos),
  .ver_pos(ver_pos)
);