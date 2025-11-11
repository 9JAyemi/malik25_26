// SVA for lcd_ctrl
// Bind into the DUT instance: bind lcd_ctrl lcd_ctrl_sva #(.WB_CLOCK_FREQUENCY(WB_CLOCK_FREQUENCY)) ();

module lcd_ctrl_sva #(parameter int WB_CLOCK_FREQUENCY = 50_000_000) ();

  // State encodings (mirror DUT)
  localparam [3:0]
    LCD_RESET   = 4'h0,
    START_DELAY = 4'h1,
    IDLE        = 4'h2,
    DELAY_INIT  = 4'h3,
    START_XFER  = 4'h4,
    CLK_PULSE_0 = 4'h5,
    CLK_PULSE_1 = 4'h6,
    DONE        = 4'h7,
    WAIT        = 4'h8;

  localparam int BIT_DELAY     = 100 * (WB_CLOCK_FREQUENCY / 1_000_000);
  localparam int STARTUP_DELAY = 100 * (WB_CLOCK_FREQUENCY / 1_000);
  localparam int RESET_DELAY   = 20  * (WB_CLOCK_FREQUENCY / 1_000);
  localparam int NB_INIT_REGS  = 19;

  // Past-valid flags
  bit past_wb, past_pix, past_pix2;
  always @(posedge wb_clk_i or posedge wb_rst_i) begin
    if (wb_rst_i) past_wb <= 1'b0;
    else          past_wb <= 1'b1;
  end
  always @(posedge pixel_clk_i or posedge pixel_rst_i) begin
    if (pixel_rst_i) begin
      past_pix  <= 1'b0;
      past_pix2 <= 1'b0;
    end else begin
      past_pix  <= 1'b1;
      past_pix2 <= past_pix;
    end
  end

  //----------------------------------------------------------------------------
  // WB clock domain: reset/initialization FSM and serial signaling
  //----------------------------------------------------------------------------

  // Reset values on wb reset
  assert property (@(posedge wb_clk_i)
    wb_rst_i |-> (state==LCD_RESET && lcd_scen && !lcd_scl && lcd_sda && lcd_req && !lcd_rst_n && bit_idx==0 && cur_reg==0)
  );

  // lcd_rst_n must rise within RESET_DELAY after reset release and then stay high
  assert property (@(posedge wb_clk_i)
    past_wb && $fell(wb_rst_i) |-> ##[1:RESET_DELAY+5] lcd_rst_n
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    lcd_rst_n |=> lcd_rst_n
  );

  // SCEN low only during an active transfer/done; high elsewhere
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    lcd_scen==0 -> (state inside {DELAY_INIT,START_XFER,CLK_PULSE_0,CLK_PULSE_1,DONE})
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state inside {START_XFER,CLK_PULSE_0,CLK_PULSE_1}) |-> lcd_scen==0
  );

  // SCL level per state and never toggles when SCEN is high
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state==CLK_PULSE_0) |-> (lcd_scl==1'b0)
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state==CLK_PULSE_1) |-> (lcd_scl==1'b1)
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    $rose(lcd_scl) |-> (lcd_scen==1'b0)
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    lcd_scen==1'b1 |-> lcd_scl==1'b0
  );

  // SDA drives current bit on START_XFER and remains stable throughout both pulse states
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state==START_XFER && bit_idx<16) |-> (lcd_sda==lcd_serial_dat[15-bit_idx])
  );
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state inside {CLK_PULSE_0,CLK_PULSE_1}) |-> $stable(lcd_sda)
  );

  // Exactly 16 SCL rising edges per transfer window (at least 16 before SCEN rises; and no SCL when SCEN high)
  sequence xfer_start; $fell(lcd_scen); endsequence
  sequence scl_r; $rose(lcd_scl); endsequence
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    xfer_start |-> (scl_r[->16]) ##1 $rose(lcd_scen)
  );

  // After last bit, SDA must be 0 until SCEN rises
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    (state==START_XFER && bit_idx>=16) |-> (lcd_sda==1'b0) until_with ($rose(lcd_scen))
  );

  // Once lcd_req deasserts, no further transfers (SCEN never falls again and SCL stays low)
  assert property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    $fell(lcd_req) |-> (always (lcd_scen==1 && lcd_scl==0))
  );

  // Cover: see one full transfer
  cover property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    $fell(lcd_scen) ##0 (scl_r[->16]) ##1 $rose(lcd_scen)
  );
  // Cover: initialization completes (lcd_req drops and SCEN stays high)
  cover property (@(posedge wb_clk_i) disable iff (wb_rst_i)
    $fell(lcd_req) ##[1:STARTUP_DELAY] (lcd_scen && lcd_scl==0)
  );

  //----------------------------------------------------------------------------
  // Pixel clock domain: sync/invert and B-R-G rotation
  //----------------------------------------------------------------------------

  // Two-cycle, active-low outputs
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 |-> (hsync_n_o == ~ $past($past(hsync_i)))
  );
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 |-> (vsync_n_o == ~ $past($past(vsync_i)))
  );
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 |-> (blank_n_o == ~ $past($past(blank_i)))
  );

  // pix_count sequencing: 0->1->2->0 unless hsync edge forces reset to 0
  wire hsync_edge = (hsync_r2 && !hsync_r);
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    hsync_edge |-> (pix_count==0)
  );
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    (!hsync_edge) |-> ##1 (pix_count == (($past(pix_count)<2) ? $past(pix_count)+1 : 0))
  );

  // Data mux: B, R, G with two-cycle pipeline
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 && (pix_count==0) |-> (lcd_data_o == $past($past(b_i)))
  );
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 && (pix_count==1) |-> (lcd_data_o == $past($past(r_i)))
  );
  assert property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    past_pix2 && (pix_count==2) |-> (lcd_data_o == $past($past(g_i)))
  );

  // Cover: observe one full B->R->G rotation
  cover property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    (pix_count==0) ##1 (pix_count==1) ##1 (pix_count==2) ##1 (pix_count==0)
  );
  // Cover: hsync edge resets pix_count
  cover property (@(posedge pixel_clk_i) disable iff (pixel_rst_i)
    hsync_edge ##1 (pix_count==0)
  );

endmodule