// SVA for crosshair
module crosshair_sva (
  input  logic         clk,
  input  logic         rst,
  input  logic  [7:0]  hdmi_r,
  input  logic  [7:0]  hdmi_g,
  input  logic  [7:0]  hdmi_b,
  input  logic         hdmi_de,
  input  logic         hdmi_hs,
  input  logic         hdmi_vs,
  input  logic  [7:0]  out_r,
  input  logic  [7:0]  out_g,
  input  logic  [7:0]  out_b,
  input  logic         out_de,
  input  logic         out_hs,
  input  logic         out_vs,
  input  logic  [9:0]  centr_x,
  input  logic  [9:0]  centr_y
);

  // track valid past cycle for $past
  logic past_valid;
  always_ff @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst || !past_valid);

  // Constants are as coded
  assert property (centr_x == 10'd32 && centr_y == 10'd32);

  // When DE was 1 last cycle: red overlay and HS/VS pass-through
  assert property ($past(hdmi_de) |-> ( out_de
                                      && out_r == 8'hFF
                                      && out_g == 8'h00
                                      && out_b == 8'h00
                                      && out_hs == $past(hdmi_hs)
                                      && out_vs == $past(hdmi_vs)));

  // When DE was 0 last cycle: blank all, HS/VS low
  assert property (!$past(hdmi_de) |-> (!out_de
                                       && out_r == 8'h00
                                       && out_g == 8'h00
                                       && out_b == 8'h00
                                       && out_hs == 1'b0
                                       && out_vs == 1'b0));

  // Tight equivalences (concise mirrors)
  assert property (out_de == $past(hdmi_de));
  assert property (out_hs == ($past(hdmi_de) ? $past(hdmi_hs) : 1'b0));
  assert property (out_vs == ($past(hdmi_de) ? $past(hdmi_vs) : 1'b0));

  // No X/Z on key outputs
  assert property (!$isunknown({out_r,out_g,out_b,out_de,out_hs,out_vs}));

  // Coverage: hit both functional modes and HS/VS pass-through
  cover property ($past(hdmi_de) && out_r==8'hFF && out_g==8'h00 && out_b==8'h00);
  cover property (!$past(hdmi_de) && {out_r,out_g,out_b,out_hs,out_vs,out_de}==0);
  cover property ($past(hdmi_de) && out_hs==$past(hdmi_hs));
  cover property ($past(hdmi_de) && out_vs==$past(hdmi_vs));

endmodule

// Bind into DUT (accesses internal centr_x/centr_y)
bind crosshair crosshair_sva u_crosshair_sva (
  .clk(clk),
  .rst(rst),
  .hdmi_r(hdmi_r),
  .hdmi_g(hdmi_g),
  .hdmi_b(hdmi_b),
  .hdmi_de(hdmi_de),
  .hdmi_hs(hdmi_hs),
  .hdmi_vs(hdmi_vs),
  .out_r(out_r),
  .out_g(out_g),
  .out_b(out_b),
  .out_de(out_de),
  .out_hs(out_hs),
  .out_vs(out_vs),
  .centr_x(centr_x),
  .centr_y(centr_y)
);