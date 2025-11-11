// SVA for vgafb_ctlif
module vgafb_ctlif_sva #(
  parameter csr_addr = 4'h0,
  parameter fml_depth = 26
)(
  input  logic                 sys_clk,
  input  logic                 sys_rst,

  input  logic [13:0]          csr_a,
  input  logic                 csr_we,
  input  logic [31:0]          csr_di,
  input  logic [31:0]          csr_do,

  input  logic                 vga_rst,

  input  logic [10:0]          hres,
  input  logic [10:0]          hsync_start,
  input  logic [10:0]          hsync_end,
  input  logic [10:0]          hscan,

  input  logic [10:0]          vres,
  input  logic [10:0]          vsync_start,
  input  logic [10:0]          vsync_end,
  input  logic [10:0]          vscan,

  input  logic [fml_depth-1:0] baseaddress,
  input  logic                 baseaddress_ack,

  input  logic [17:0]          nbursts,
  input  logic [1:0]           vga_clk_sel,

  // internal
  input  logic [fml_depth-1:0] baseaddress_act
);

  default clocking cb @(posedge sys_clk); endclocking

  // Convenience
  localparam int A_VGA_RST   = 4'd0;
  localparam int A_HRES      = 4'd1;
  localparam int A_HS_STA    = 4'd2;
  localparam int A_HS_END    = 4'd3;
  localparam int A_HSCAN     = 4'd4;
  localparam int A_VRES      = 4'd5;
  localparam int A_VS_STA    = 4'd6;
  localparam int A_VS_END    = 4'd7;
  localparam int A_VSCAN     = 4'd8;
  localparam int A_BASE      = 4'd9;
  localparam int A_BASE_ACT  = 4'd10;
  localparam int A_NBURSTS   = 4'd11;
  localparam int A_CLKSEL    = 4'd12;

  wire sel = (csr_a[13:10] == csr_addr);
  wire [3:0] a_lo = csr_a[3:0];

  // Reset defaults
  assert property (@cb sys_rst |-> (
      csr_do == 32'd0 &&
      vga_rst == 1'b1 &&
      hres == 11'd640 &&
      hsync_start == 11'd656 &&
      hsync_end == 11'd752 &&
      hscan == 11'd799 &&
      vres == 11'd480 &&
      vsync_start == 11'd491 &&
      vsync_end == 11'd493 &&
      vscan == 11'd523 &&
      baseaddress == {fml_depth{1'b0}} &&
      baseaddress_act == {fml_depth{1'b0}} &&
      nbursts == 18'd19200 &&
      vga_clk_sel == 2'b00
  ));

  // Register write updates (take effect next cycle)
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_VGA_RST) |=> vga_rst == $past(csr_di[0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_HRES) |=> hres == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_HS_STA) |=> hsync_start == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_HS_END) |=> hsync_end == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_HSCAN) |=> hscan == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_VRES) |=> vres == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_VS_STA) |=> vsync_start == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_VS_END) |=> vsync_end == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_VSCAN) |=> vscan == $past(csr_di[10:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_BASE) |=> baseaddress == $past(csr_di[fml_depth-1:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_NBURSTS) |=> nbursts == $past(csr_di[17:0])
  );
  assert property (@cb disable iff (sys_rst)
    sel && csr_we && (a_lo == A_CLKSEL) |=> vga_clk_sel == $past(csr_di[1:0])
  );

  // Stability when not being written (per-register)
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_VGA_RST)) |=> $stable(vga_rst)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_HRES)) |=> $stable(hres)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_HS_STA)) |=> $stable(hsync_start)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_HS_END)) |=> $stable(hsync_end)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_HSCAN)) |=> $stable(hscan)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_VRES)) |=> $stable(vres)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_VS_STA)) |=> $stable(vsync_start)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_VS_END)) |=> $stable(vsync_end)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_VSCAN)) |=> $stable(vscan)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_BASE)) |=> $stable(baseaddress)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_NBURSTS)) |=> $stable(nbursts)
  );
  assert property (@cb disable iff (sys_rst)
    !(sel && csr_we && (a_lo == A_CLKSEL)) |=> $stable(vga_clk_sel)
  );

  // Read mux behavior when selected and not writing (zero-extended)
  assert property (@cb (sel && !csr_we && a_lo == A_VGA_RST) |-> (csr_do[0] == vga_rst && csr_do[31:1] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_HRES)    |-> (csr_do[10:0] == hres && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_HS_STA)  |-> (csr_do[10:0] == hsync_start && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_HS_END)  |-> (csr_do[10:0] == hsync_end && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_HSCAN)   |-> (csr_do[10:0] == hscan && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_VRES)    |-> (csr_do[10:0] == vres && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_VS_STA)  |-> (csr_do[10:0] == vsync_start && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_VS_END)  |-> (csr_do[10:0] == vsync_end && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_VSCAN)   |-> (csr_do[10:0] == vscan && csr_do[31:11] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_BASE)    |-> (csr_do[fml_depth-1:0] == baseaddress && csr_do[31:fml_depth] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_BASE_ACT)|-> (csr_do[fml_depth-1:0] == baseaddress_act && csr_do[31:fml_depth] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_NBURSTS) |-> (csr_do[17:0] == nbursts && csr_do[31:18] == '0));
  assert property (@cb (sel && !csr_we && a_lo == A_CLKSEL)  |-> (csr_do[1:0] == vga_clk_sel && csr_do[31:2] == '0));

  // csr_do is zero when not selected or invalid address
  assert property (@cb (!sel) |-> (csr_do == 32'd0));
  assert property (@cb (sel && (a_lo inside {4'd13,4'd14,4'd15})) |-> (csr_do == 32'd0));

  // baseaddress_act handshake behavior
  assert property (@cb disable iff (sys_rst)
    !baseaddress_ack |=> $stable(baseaddress_act)
  );
  assert property (@cb disable iff (sys_rst)
    baseaddress_ack |=> (baseaddress_act == $past(baseaddress))
  );

  // Timing/geometry sanity (monotonic ranges)
  assert property (@cb disable iff (sys_rst)
    (hres <= hsync_start) && (hsync_start <= hsync_end) && (hsync_end <= hscan)
  );
  assert property (@cb disable iff (sys_rst)
    (vres <= vsync_start) && (vsync_start <= vsync_end) && (vsync_end <= vscan)
  );

  // Coverage
  cover property (@cb sel && csr_we && (a_lo == A_VGA_RST));
  cover property (@cb sel && csr_we && (a_lo == A_HRES));
  cover property (@cb sel && csr_we && (a_lo == A_HS_STA));
  cover property (@cb sel && csr_we && (a_lo == A_HS_END));
  cover property (@cb sel && csr_we && (a_lo == A_HSCAN));
  cover property (@cb sel && csr_we && (a_lo == A_VRES));
  cover property (@cb sel && csr_we && (a_lo == A_VS_STA));
  cover property (@cb sel && csr_we && (a_lo == A_VS_END));
  cover property (@cb sel && csr_we && (a_lo == A_VSCAN));
  cover property (@cb sel && csr_we && (a_lo == A_BASE));
  cover property (@cb sel && !csr_we && (a_lo == A_BASE_ACT));
  cover property (@cb sel && csr_we && (a_lo == A_NBURSTS));
  cover property (@cb sel && csr_we && (a_lo == A_CLKSEL));

  cover property (@cb baseaddress_ack ##1 (baseaddress_act == $past(baseaddress)));

  cover property (@cb (sel && !csr_we && (a_lo inside {4'd13,4'd14,4'd15}) && csr_do == 32'd0));
  cover property (@cb (!sel && csr_do == 32'd0));

  // Cover: post-reset default configuration observed
  cover property (@cb $fell(sys_rst) ##1 (
    vga_rst == 1'b1 &&
    hres == 11'd640 && hsync_start == 11'd656 && hsync_end == 11'd752 && hscan == 11'd799 &&
    vres == 11'd480 && vsync_start == 11'd491 && vsync_end == 11'd493 && vscan == 11'd523 &&
    baseaddress == {fml_depth{1'b0}} && nbursts == 18'd19200 && vga_clk_sel == 2'b00
  ));

endmodule

// Bind into DUT
bind vgafb_ctlif vgafb_ctlif_sva #(.csr_addr(csr_addr), .fml_depth(fml_depth)) vgafb_ctlif_sva_i (.*);