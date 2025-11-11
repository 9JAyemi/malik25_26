// SVA checker for vga_controller
// Bind example:
// bind vga_controller vga_controller_sva #() u_vga_controller_sva (.*,
//     .pixel_cnt(pixel_cnt), .line_cnt(line_cnt));

module vga_controller_sva #(
  parameter int HD = 640, HF = 16, HS = 96, HT = 800,
                 VD = 480, VF = 10, VS = 2,  VT = 525
)(
  input  logic        pclk, reset,
  input  logic        hsync, vsync, valid,
  input  logic [9:0]  h_cnt, v_cnt,
  // internal DUT state (bind to these)
  input  logic [9:0]  pixel_cnt, line_cnt
);

  // derived boundaries (inclusive start, exclusive end)
  localparam int HS_LO_START = HD + HF - 1;
  localparam int HS_LO_END   = HD + HF + HS - 1;
  localparam int VS_LO_START = VD + VF - 1;
  localparam int VS_LO_END   = VD + VF + VS - 1;

  logic past_ok;
  always_ff @(posedge pclk) past_ok <= !reset;

  default clocking cb @(posedge pclk); endclocking
  default disable iff (reset);

  // Convenience windows
  wire hs_low_w = (pixel_cnt >= HS_LO_START) && (pixel_cnt < HS_LO_END);
  wire vs_low_w = (line_cnt  >= VS_LO_START) && (line_cnt  < VS_LO_END);

  // Reset behavior
  assert property (reset |-> pixel_cnt==10'd0 && line_cnt==10'd0 &&
                             hsync==1'b1 && vsync==1'b1 &&
                             !valid && h_cnt==10'd0 && v_cnt==10'd0);

  // pixel_cnt: range, step, wrap
  assert property (pixel_cnt < HT);
  assert property (past_ok && $past(pixel_cnt) < HT-1 |-> pixel_cnt == $past(pixel_cnt) + 10'd1);
  assert property (past_ok && $past(pixel_cnt) == HT-1 |-> pixel_cnt == 10'd0);

  // line_cnt: range, hold between EOLs, step/wrap at EOL
  assert property (line_cnt < VT);
  assert property (past_ok && $past(pixel_cnt) != HT-1 |-> line_cnt == $past(line_cnt));
  assert property (past_ok && $past(pixel_cnt) == HT-1 && $past(line_cnt) < VT-1
                   |-> line_cnt == $past(line_cnt) + 10'd1);
  assert property (past_ok && $past(pixel_cnt) == HT-1 && $past(line_cnt) == VT-1
                   |-> line_cnt == 10'd0);

  // H/V sync exact decode
  assert property (hsync == !hs_low_w);
  assert property (vsync == !vs_low_w);

  // H/V sync widths/alignment
  assert property ((pixel_cnt == HS_LO_START) |-> (hsync==1'b0)[*HS] ##1 (hsync==1'b1));

  // Valid region exact decode
  assert property (valid == ((pixel_cnt < HD) && (line_cnt < VD)));

  // h_cnt/v_cnt mapping and zeroing out of range
  assert property (h_cnt == ((pixel_cnt < HD) ? pixel_cnt : 10'd0));
  assert property (v_cnt == ((line_cnt  < VD) ? line_cnt  : 10'd0));
  assert property ((pixel_cnt >= HD) |-> h_cnt == 10'd0);
  assert property ((line_cnt  >= VD) |-> v_cnt == 10'd0);

  // Safety: outputs within expected bounds
  assert property (h_cnt <= (HD-1));
  assert property (v_cnt <= (VD-1));

  // Basic functional coverage
  cover property (past_ok && $past(pixel_cnt)==HT-1 ##1 pixel_cnt==10'd0);                       // line wrap
  cover property (past_ok && $past(pixel_cnt)==HT-1 && $past(line_cnt)==VT-1 ##1 line_cnt==0);   // frame wrap
  cover property (pixel_cnt==HS_LO_START && $fell(hsync));                                       // hsync fall
  cover property (pixel_cnt==HS_LO_END   && $rose(hsync));                                       // hsync rise
  cover property ($fell(vsync));                                                                  // vsync fall
  cover property ($rose(vsync));                                                                  // vsync rise
  cover property (valid);                                                                         // any active video
  cover property (pixel_cnt==HD-1 && line_cnt==VD-1 && valid);                                    // last active pixel

endmodule