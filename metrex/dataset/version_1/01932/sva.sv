// SVA for gpio
// Bind this file to the DUT:
//   bind gpio gpio_sva gpio_sva_i (.*);

module gpio_sva (
  input         wb_clk,
  input         wb_rst,
  input         wb_adr_i,
  input  [7:0]  wb_dat_i,
  input         wb_we_i,
  input         wb_cyc_i,
  input         wb_stb_i,
  input  [2:0]  wb_cti_i,
  input  [1:0]  wb_bte_i,
  output [7:0]  wb_dat_o,
  output        wb_ack_o,
  output        wb_err_o,
  output        wb_rty_o,
  input  [7:0]  gpio_i,
  output [7:0]  gpio_o,
  output [7:0]  gpio_dir_o
);

  // Helpful shorthands
  wire req    = wb_cyc_i & wb_stb_i;
  wire wr     = req & wb_we_i;
  wire rd     = req & ~wb_we_i;
  wire w_gpo  = wr & (wb_adr_i == 1'b0);
  wire w_dir  = wr & (wb_adr_i == 1'b1);
  wire a0     = (wb_adr_i == 1'b0);
  wire a1     = (wb_adr_i == 1'b1);

  // ----------------------------
  // Reset behavior
  // ----------------------------
  // Registers reset to zero on the cycle after reset asserted
  assert property (@(posedge wb_clk) wb_rst |=> (gpio_o == '0));
  assert property (@(posedge wb_clk) wb_rst |=> (gpio_dir_o == '0));
  assert property (@(posedge wb_clk) wb_rst |=> (wb_ack_o == 1'b0));
  // Error/Retry permanently zero
  assert property (@(posedge wb_clk) wb_err_o == 1'b0);
  assert property (@(posedge wb_clk) wb_rty_o == 1'b0);

  // ----------------------------
  // Wishbone handshake (classic, single-cycle ack pulse)
  // ----------------------------
  // Any new request when ack is low is acknowledged next cycle
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (req & ~wb_ack_o) |=> wb_ack_o);

  // Ack is a single-cycle pulse
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    wb_ack_o |=> !wb_ack_o);

  // Ack only occurs if there was a request in the previous cycle
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    wb_ack_o |-> $past(req));

  // ----------------------------
  // Register write behavior
  // ----------------------------
  // Write to data-out register
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    w_gpo |=> (gpio_o == $past(wb_dat_i)));

  // Write to direction register
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    w_dir |=> (gpio_dir_o == $past(wb_dat_i)));

  // No unintended updates: a change implies a write to that register in prior cycle
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (gpio_o != $past(gpio_o)) |-> $past(w_gpo));

  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (gpio_dir_o != $past(gpio_dir_o)) |-> $past(w_dir));

  // ----------------------------
  // Read datapath (registered read mux)
  // wb_dat_o gets updated every cycle based on address bit
  // ----------------------------
  // Next-cycle wb_dat_o reflects selected source sampled in previous cycle
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    a0 |=> (wb_dat_o == $past(gpio_i)));

  assert property (@(posedge wb_clk) disable iff (wb_rst)
    a1 |=> (wb_dat_o == $past(gpio_dir_o)));

  // During a read acknowledge, data must correspond to the selected source
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (wb_ack_o & $past(rd) & $past(a0)) |-> (wb_dat_o == (a0 ? $past(gpio_i)      : wb_dat_o)));

  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (wb_ack_o & $past(rd) & $past(a1)) |-> (wb_dat_o == (a1 ? $past(gpio_dir_o) : wb_dat_o)));

  // ----------------------------
  // Basic X-checks on key outputs during operation
  // ----------------------------
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    !$isunknown({wb_ack_o, wb_err_o, wb_rty_o, gpio_o, gpio_dir_o}));

  // Optionally ensure read data is known when acknowledging a read
  assert property (@(posedge wb_clk) disable iff (wb_rst)
    (wb_ack_o & $past(rd)) |-> !$isunknown(wb_dat_o));

  // ----------------------------
  // Coverage
  // ----------------------------
  // Reset -> writes to both regs -> reads from both addresses with acks
  cover property (@(posedge wb_clk)
    wb_rst ##1 !wb_rst ##1
    (w_dir, 1) ##1 (w_gpo, 1) ##1
    (rd & a0) ##1 wb_ack_o ##1
    (rd & a1) ##1 wb_ack_o);

  // Exercise continuous request producing alternating acks
  cover property (@(posedge wb_clk) disable iff (wb_rst)
    req ##1 wb_ack_o ##1 !wb_ack_o ##1 wb_ack_o);

  // Cover direction bit toggling and data-out change
  cover property (@(posedge wb_clk) disable iff (wb_rst)
    w_dir ##1 (gpio_dir_o != $past(gpio_dir_o)));

  cover property (@(posedge wb_clk) disable iff (wb_rst)
    w_gpo ##1 (gpio_o != $past(gpio_o)));

endmodule