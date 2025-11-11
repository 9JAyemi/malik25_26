// SVA for vga512x256
// Bind this module to the DUT to check internal behavior
module vga512x256_sva #(
  parameter int B = 50, C = 92, D = 512, E = 36,
  parameter int P = 4,  Q = 61, R = 512, S = 31
)(
  input  logic        clk,
  input  logic        rst,
  input  logic [12:0] maddr,
  input  logic [15:0] mdata,
  input  logic        red, green, blue,
  input  logic        hsync, vsync,
  // internal DUT signals (bind to these)
  input  logic [9:0]  cnt_x,
  input  logic [9:0]  cnt_y,
  input  logic [15:0] word
);

  default clocking cb @(posedge clk); endclocking

  localparam int H_TOTAL = B + C + D + E;
  localparam int V_TOTAL = P + Q + R + S;

  // Reset effect on counters (must be checked even during rst)
  property p_rst_sync;
    @(posedge clk) rst |=> (cnt_x == 0 && cnt_y == 0);
  endproperty
  assert property(p_rst_sync);

  // Basic counter ranges
  assert property (@cb disable iff (rst) cnt_x < H_TOTAL);
  assert property (@cb disable iff (rst) cnt_y < V_TOTAL);

  // cnt_x increments then wraps
  assert property (@cb disable iff (rst)
    ($past(cnt_x) != H_TOTAL-1) |-> (cnt_x == $past(cnt_x) + 1)
  );
  assert property (@cb disable iff (rst)
    ($past(cnt_x) == H_TOTAL-1) |-> (cnt_x == 0)
  );

  // cnt_y holds within line, increments on end-of-line, wraps on end-of-frame
  assert property (@cb disable iff (rst)
    ($past(cnt_x) != H_TOTAL-1) |-> (cnt_y == $past(cnt_y))
  );
  assert property (@cb disable iff (rst)
    ($past(cnt_x) == H_TOTAL-1 && $past(cnt_y) != V_TOTAL-1) |-> (cnt_y == $past(cnt_y) + 1)
  );
  assert property (@cb disable iff (rst)
    ($past(cnt_x) == H_TOTAL-1 && $past(cnt_y) == V_TOTAL-1) |-> (cnt_y == 0)
  );

  // Sync polarities and windows
  assert property (@cb disable iff (rst)
    hsync === ~((cnt_x > (D + E)) && (cnt_x <= (D + E + B)))
  );
  assert property (@cb disable iff (rst)
    vsync === ~((cnt_y >= (R + S)) && (cnt_y <  (R + S + P)))
  );

  // Color outputs derive from word[0] and match each other
  assert property (@cb disable iff (rst)
    (red === word[0]) && (green === word[0]) && (blue === word[0])
  );

  // Address mapping
  assert property (@cb disable iff (rst)
    maddr == { cnt_y[8:1], cnt_x[8:4] }
  );

  // word load and shift behavior
  // Load active pixels
  assert property (@cb disable iff (rst)
    (cnt_x[3:0] == 4'h1 && (cnt_x <= D) && (cnt_y < R)) |=> (word == $past(mdata))
  );
  // Load zero during blank
  assert property (@cb disable iff (rst)
    (cnt_x[3:0] == 4'h1 && !((cnt_x <= D) && (cnt_y < R))) |=> (word == 16'h0)
  );
  // Shift right with zero fill otherwise
  assert property (@cb disable iff (rst)
    (cnt_x[3:0] != 4'h1) |=> (word == {1'b0, $past(word[15:1])})
  );

  // Coverage (key milestones)
  // End-of-line and end-of-frame events
  cover property (@cb disable iff (rst) ($past(cnt_x) == H_TOTAL-1) ##1 (cnt_x == 0));
  cover property (@cb disable iff (rst)
    ($past(cnt_x) == H_TOTAL-1 && $past(cnt_y) == V_TOTAL-1) ##1 (cnt_x == 0 && cnt_y == 0)
  );

  // Observe hsync and vsync pulses
  cover property (@cb disable iff (rst) $fell(hsync) ##[1:$] $rose(hsync));
  cover property (@cb disable iff (rst) $fell(vsync) ##[1:$] $rose(vsync));

  // Observe active-area fetch and blank-area zero-load
  cover property (@cb disable iff (rst) (cnt_x[3:0]==4'h1 && (cnt_x<=D) && (cnt_y<R)));
  cover property (@cb disable iff (rst) (cnt_x[3:0]==4'h1 && !((cnt_x<=D) && (cnt_y<R))));

endmodule

// Example bind (instantiate once per DUT instance)
// bind vga512x256 vga512x256_sva #(.B(B),.C(C),.D(D),.E(E),.P(P),.Q(Q),.R(R),.S(S)) i_vga_sva (
//   .clk(clk), .rst(rst), .maddr(maddr), .mdata(mdata),
//   .red(red), .green(green), .blue(blue), .hsync(hsync), .vsync(vsync),
//   .cnt_x(cnt_x), .cnt_y(cnt_y), .word(word)
// );