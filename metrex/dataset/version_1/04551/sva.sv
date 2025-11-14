//=========================================================
// SVA for hdmi_circle and circle
// Concise, high-value checks + coverage
//=========================================================
`ifndef HDMI_CIRCLE_SVA
`define HDMI_CIRCLE_SVA

//------------------------------
// Bind: hdmi_circle
//------------------------------
module hdmi_circle_sva (
    input  logic              clk,
    input  logic              hdmi_vs,
    input  logic              hdmi_de,
    input  logic              hdmi_vs_out,
    input  logic              hdmi_de_out,
    input  logic [7:0]        hdmi_r,
    input  logic [7:0]        hdmi_g,
    input  logic [7:0]        hdmi_b,
    input  logic [7:0]        data_out,
    input  logic              inside_circle,
    input  logic [7:0]        r_out,
    input  logic [7:0]        g_out,
    input  logic [7:0]        b_out
);
  default clocking cb @(posedge clk); endclocking

  // avoid $past underflow
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Passthrough checks
  assert property (hdmi_vs_out == hdmi_vs);
  assert property (hdmi_de_out == hdmi_de);

  // Colorization behavior
  assert property (past_valid && inside_circle |=> r_out == 8'hFF && g_out == 8'h00 && b_out == 8'h00);
  assert property (past_valid && !inside_circle |=> r_out == $past(hdmi_r) && g_out == $past(hdmi_g) && b_out == $past(hdmi_b));

  // Note: hdmi_data_out is 8 bits in DUT; assignment truncates to blue channel.
  // This assertion both documents and checks the effective behavior.
  assert property (data_out == (inside_circle ? 8'h00 : hdmi_b));

  // Coverage
  cover property (inside_circle);
  cover property (!inside_circle);
  cover property (inside_circle ##1 !inside_circle);
  cover property (!inside_circle ##1 inside_circle);
  cover property (!inside_circle |=> r_out == $past(hdmi_r) && g_out == $past(hdmi_g) && b_out == $past(hdmi_b));
  cover property (inside_circle |=> r_out == 8'hFF && g_out == 8'h00 && b_out == 8'h00);
endmodule

bind hdmi_circle hdmi_circle_sva hdc_sva (
  .clk          (hdmi_clk),
  .hdmi_vs      (hdmi_vs),
  .hdmi_de      (hdmi_de),
  .hdmi_vs_out  (hdmi_vs_out),
  .hdmi_de_out  (hdmi_de_out),
  .hdmi_r       (hdmi_r),
  .hdmi_g       (hdmi_g),
  .hdmi_b       (hdmi_b),
  .data_out     (hdmi_data_out),
  .inside_circle(inside_circle),
  .r_out        (hdmi_r_out),
  .g_out        (hdmi_g_out),
  .b_out        (hdmi_b_out)
);

//------------------------------
// Bind: circle
//------------------------------
module circle_sva (
    input  logic              clk,
    input  logic              rst,
    input  logic              ce,
    input  logic [9:0]        x,
    input  logic [9:0]        y,
    input  logic [9:0]        x_count,
    input  logic [9:0]        y_count,
    input  logic              inside_circle,
    input  logic [9:0]        CENTER_X,
    input  logic [9:0]        CENTER_Y,
    input  logic [9:0]        RADIUS,
    input  logic [9:0]        c_w,   // treated as width of line
    input  logic [9:0]        c_h    // not used by DUT logic, but kept for completeness
);
  default clocking cb @(posedge clk); endclocking

  // avoid $past underflow and disable during reset
  logic past_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // x,y must reflect counters when ce is asserted; hold when ce deasserted
  assert property (disable iff (rst) ce |-> (x == x_count && y == y_count));
  assert property (disable iff (rst) !ce |=> $stable(x) && $stable(y) && $stable(inside_circle));

  // Geometric correctness
  function automatic logic in_circle(logic [9:0] xi, yi, cx, cy, r);
    logic signed [10:0] dx, dy;
    logic [21:0] dx2, dy2, r2;
    begin
      dx  = $signed({1'b0,xi}) - $signed({1'b0,cx});
      dy  = $signed({1'b0,yi}) - $signed({1'b0,cy});
      dx2 = dx*dx;
      dy2 = dy*dy;
      r2  = (r*r);
      in_circle = (dx2 + dy2) <= r2;
    end
  endfunction

  assert property (disable iff (rst) ce |-> inside_circle == in_circle(x, y, CENTER_X, CENTER_Y, RADIUS));

  // Counter next-state behavior
  // Increment when not at end-of-line
  assert property (disable iff (rst || !past_valid)
                   ce && $past(ce) && ($past(x_count) != c_w)
                   |=> (x_count == $past(x_count) + 10'd1) && (y_count == $past(y_count)));

  // Wrap and bump y at end-of-line
  assert property (disable iff (rst || !past_valid)
                   ce && $past(ce) && ($past(x_count) == c_w)
                   |=> (x_count == 10'd0) && (y_count == $past(y_count) + 10'd1));

  // y_count should only increment on x wrap
  assert property (disable iff (rst || !past_valid)
                   ce && $past(ce) && (y_count == $past(y_count) + 10'd1)
                   |-> ($past(x_count) == c_w));

  // Coverage: see wrap, center point, inside/outside
  cover property (ce && x_count == c_w ##1 x_count == 10'd0 && y_count == $past(y_count)+10'd1);
  cover property (ce && x == CENTER_X && y == CENTER_Y && inside_circle);
  cover property (ce && !inside_circle);
  cover property (ce && inside_circle);
endmodule

bind circle circle_sva circ_sva (
  .clk         (clk),
  .rst         (rst),
  .ce          (ce),
  .x           (x),
  .y           (y),
  .x_count     (x_count),
  .y_count     (y_count),
  .inside_circle(inside_circle),
  .CENTER_X    (CENTER_X),
  .CENTER_Y    (CENTER_Y),
  .RADIUS      (RADIUS),
  .c_w         (c_w),
  .c_h         (c_h)
);

`endif // HDMI_CIRCLE_SVA