// SVA for ecfg. Bind this file to the DUT.
// Strong checks for decode, reset behavior, register R/W side-effects, output mapping, and read data.
// Includes compact functional coverage.

module ecfg_sva
  #(parameter IDW=12)
(
  input  logic                clk,
  input  logic                hw_reset,

  // bus
  input  logic                mi_access,
  input  logic                mi_write,
  input  logic [19:0]         mi_addr,
  input  logic [31:0]         mi_data_in,
  input  logic [31:0]         mi_data_out,
  input  logic                mi_data_sel,
  input  logic [IDW-1:0]      param_coreid,

  // DUT outputs
  input  logic                ecfg_sw_reset,
  input  logic                ecfg_reset,
  input  logic                ecfg_tx_enable,
  input  logic                ecfg_tx_mmu_mode,
  input  logic                ecfg_tx_gpio_mode,
  input  logic [3:0]          ecfg_tx_ctrl_mode,
  input  logic [3:0]          ecfg_tx_clkdiv,
  input  logic                ecfg_rx_enable,
  input  logic                ecfg_rx_mmu_mode,
  input  logic                ecfg_rx_gpio_mode,
  input  logic                ecfg_rx_loopback_mode,
  input  logic                ecfg_cclk_en,
  input  logic [3:0]          ecfg_cclk_div,
  input  logic [3:0]          ecfg_cclk_pllcfg,
  input  logic [IDW-1:0]      ecfg_coreid,
  input  logic [11:0]         ecfg_gpio_dataout,

  // internal regs/wires
  input  logic [11:0]         ecfg_cfgtx_reg,
  input  logic [4:0]          ecfg_cfgrx_reg,
  input  logic [7:0]          ecfg_cfgclk_reg,
  input  logic [IDW-1:0]      ecfg_coreid_reg,
  input  logic [31:0]         ecfg_version_reg,
  input  logic                ecfg_reset_reg,
  input  logic [11:0]         ecfg_gpio_datain_reg,
  input  logic [11:0]         ecfg_gpio_dataout_reg,

  input  logic                ecfg_write,
  input  logic                ecfg_read,

  input  logic                ecfg_reset_match,
  input  logic                ecfg_cfgtx_match,
  input  logic                ecfg_cfgrx_match,
  input  logic                ecfg_cfgclk_match,
  input  logic                ecfg_coreid_match,
  input  logic                ecfg_version_match,
  input  logic                ecfg_datain_match,
  input  logic                ecfg_dataout_match,
  input  logic                ecfg_match,

  input  logic [31:0]         ecfg_reg_mux,

  input  logic                ecfg_cfgtx_write,
  input  logic                ecfg_cfgrx_write,
  input  logic                ecfg_cfgclk_write,
  input  logic                ecfg_coreid_write,
  input  logic                ecfg_version_write,
  input  logic                ecfg_datain_write,
  input  logic                ecfg_dataout_write,
  input  logic                ecfg_reset_write,

  input  logic                ecfg_rx_monitor_mode
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (hw_reset);

  // Address decode sanity
  assert property ( $onehot0({
      ecfg_reset_match, ecfg_cfgtx_match, ecfg_cfgrx_match, ecfg_cfgclk_match,
      ecfg_coreid_match, ecfg_version_match, ecfg_datain_match, ecfg_dataout_match}) );

  assert property ( ecfg_match == (ecfg_reset_match   | ecfg_cfgtx_match | ecfg_cfgrx_match |
                                   ecfg_cfgclk_match  | ecfg_coreid_match| ecfg_version_match |
                                   ecfg_datain_match  | ecfg_dataout_match) );

  // Write strobe correctness
  assert property ( (ecfg_write && ecfg_match) |-> $onehot({
      ecfg_reset_write, ecfg_cfgtx_write, ecfg_cfgrx_write, ecfg_cfgclk_write,
      ecfg_coreid_write, ecfg_version_write, ecfg_datain_write, ecfg_dataout_write}) );

  assert property ( (ecfg_write && !ecfg_match) |-> !(
      ecfg_reset_write | ecfg_cfgtx_write | ecfg_cfgrx_write | ecfg_cfgclk_write |
      ecfg_coreid_write | ecfg_version_write | ecfg_datain_write | ecfg_dataout_write) );

  // Registers only change on their write (stable otherwise)
  assert property ( !ecfg_cfgtx_write |=> $stable(ecfg_cfgtx_reg) );
  assert property ( !ecfg_cfgrx_write |=> $stable(ecfg_cfgrx_reg) );
  assert property ( !ecfg_cfgclk_write |=> $stable(ecfg_cfgclk_reg) );
  assert property ( !ecfg_coreid_write |=> $stable(ecfg_coreid_reg) );
  assert property ( !ecfg_datain_write |=> $stable(ecfg_gpio_datain_reg) );
  assert property ( !ecfg_dataout_write |=> $stable(ecfg_gpio_dataout_reg) );
  assert property ( !ecfg_reset_write |=> $stable(ecfg_reset_reg) );

  // Write effects (next cycle takes past data)
  assert property ( ecfg_cfgtx_write  |=> ecfg_cfgtx_reg       == $past(mi_data_in[11:0]) );
  assert property ( ecfg_cfgrx_write  |=> ecfg_cfgrx_reg       == $past(mi_data_in[4:0]) );
  assert property ( ecfg_cfgclk_write |=> ecfg_cfgclk_reg      == $past(mi_data_in[7:0]) );
  assert property ( ecfg_coreid_write |=> ecfg_coreid_reg      == $past(mi_data_in[IDW-1:0]) );
  assert property ( ecfg_datain_write |=> ecfg_gpio_datain_reg == $past(mi_data_in[11:0]) );
  assert property ( ecfg_dataout_write|=> ecfg_gpio_dataout_reg== $past(mi_data_in[11:0]) );
  assert property ( ecfg_reset_write  |=> ecfg_reset_reg       == $past(mi_data_in[0]) );

  // Writing VERSION has no side effects and constant value is preserved
  assert property ( 1 |-> ecfg_version_reg == 32'h01_02_03_04 );
  assert property ( ecfg_version_write |=> $stable({
      ecfg_cfgtx_reg, ecfg_cfgrx_reg, ecfg_cfgclk_reg, ecfg_coreid_reg,
      ecfg_gpio_datain_reg, ecfg_gpio_dataout_reg, ecfg_reset_reg}) );

  // Reset behavior (synchronous)
  // Checked on cycle after hw_reset assertion (no disable iff)
  assert property (@(posedge clk) hw_reset |=> ecfg_cfgtx_reg        == 12'h000 );
  assert property (@(posedge clk) hw_reset |=> ecfg_cfgrx_reg        == 5'h00 );
  assert property (@(posedge clk) hw_reset |=> ecfg_cfgclk_reg       == 8'h00 );
  assert property (@(posedge clk) hw_reset |=> ecfg_coreid_reg       == param_coreid );
  assert property (@(posedge clk) hw_reset |=> ecfg_gpio_datain_reg  == 12'h000 );
  assert property (@(posedge clk) hw_reset |=> ecfg_gpio_dataout_reg == 12'h000 );
  assert property (@(posedge clk) hw_reset |=> ecfg_reset_reg        == 1'b0 );

  // Output mapping and decodes
  assert property ( ecfg_tx_enable     == ecfg_cfgtx_reg[0] );
  assert property ( ecfg_tx_mmu_mode   == ecfg_cfgtx_reg[1] );
  assert property ( ecfg_tx_gpio_mode  == (ecfg_cfgtx_reg[3:2] == 2'b01) );
  assert property ( ecfg_tx_ctrl_mode  == ecfg_cfgtx_reg[7:4] );
  assert property ( ecfg_tx_clkdiv     == ecfg_cfgtx_reg[11:8] );

  assert property ( ecfg_rx_enable        == ecfg_cfgrx_reg[0] );
  assert property ( ecfg_rx_mmu_mode      == ecfg_cfgrx_reg[1] );
  assert property ( ecfg_rx_gpio_mode     == (ecfg_cfgrx_reg[3:2] == 2'b01) );
  assert property ( ecfg_rx_loopback_mode == (ecfg_cfgrx_reg[3:2] == 2'b10) );
  assert property ( !(ecfg_rx_gpio_mode && ecfg_rx_loopback_mode) );

  assert property ( ecfg_rx_monitor_mode  == ecfg_cfgrx_reg[4] );

  assert property ( ecfg_cclk_div    == ecfg_cfgclk_reg[3:0] );
  assert property ( ecfg_cclk_pllcfg == ecfg_cfgclk_reg[7:4] );
  assert property ( ecfg_cclk_en     == (ecfg_cclk_div != 4'b0000) );

  assert property ( ecfg_coreid      == ecfg_coreid_reg );
  assert property ( ecfg_gpio_dataout== ecfg_gpio_dataout_reg );

  assert property ( ecfg_sw_reset == ecfg_reset_reg );
  assert property ( ecfg_reset    == (ecfg_sw_reset | hw_reset) );

  // Read path timing and correctness
  assert property ( ecfg_read |=> ( mi_data_out == $past(ecfg_reg_mux)
                                    && mi_data_sel == $past(ecfg_match) ) );

  // Strong spec checks for read-data contents per address
  // Note: If these fail, the address-to-register muxing is wrong.
  assert property ( (ecfg_read && ecfg_reset_match)  |=> (mi_data_out == {31'b0, $past(ecfg_reset_reg)}) );
  assert property ( (ecfg_read && ecfg_cfgtx_match)  |=> (mi_data_out == {20'b0, $past(ecfg_cfgtx_reg)}) );
  assert property ( (ecfg_read && ecfg_cfgrx_match)  |=> (mi_data_out == {27'b0, $past(ecfg_cfgrx_reg)}) );
  assert property ( (ecfg_read && ecfg_cfgclk_match) |=> (mi_data_out == {24'b0, $past(ecfg_cfgclk_reg)}) );
  assert property ( (ecfg_read && ecfg_coreid_match) |=> (mi_data_out == {20'b0, $past(ecfg_coreid_reg)}) );
  assert property ( (ecfg_read && ecfg_version_match)|=> (mi_data_out ==  $past(ecfg_version_reg)) );
  assert property ( (ecfg_read && ecfg_datain_match) |=> (mi_data_out == {20'b0, $past(ecfg_gpio_datain_reg)}) );
  assert property ( (ecfg_read && ecfg_dataout_match)|=> (mi_data_out == {20'b0, $past(ecfg_gpio_dataout_reg)}) );

  // Minimal functional coverage
  cover property ( ecfg_cfgtx_write );
  cover property ( ecfg_cfgrx_write );
  cover property ( ecfg_cfgclk_write );
  cover property ( ecfg_coreid_write );
  cover property ( ecfg_datain_write );
  cover property ( ecfg_dataout_write );
  cover property ( ecfg_reset_write );
  cover property ( ecfg_version_write );

  cover property ( ecfg_read && ecfg_cfgtx_match );
  cover property ( ecfg_read && ecfg_cfgrx_match );
  cover property ( ecfg_read && ecfg_cfgclk_match );
  cover property ( ecfg_read && ecfg_coreid_match );
  cover property ( ecfg_read && ecfg_version_match );
  cover property ( ecfg_read && ecfg_datain_match );
  cover property ( ecfg_read && ecfg_dataout_match );
  cover property ( ecfg_read && ecfg_reset_match );

  cover property ( $rose(ecfg_cclk_en) );
  cover property ( $fell(ecfg_cclk_en) );

  cover property ( ecfg_rx_gpio_mode );
  cover property ( ecfg_rx_loopback_mode );
  cover property ( ecfg_cfgrx_reg[3:2]==2'b00 );
  cover property ( ecfg_cfgrx_reg[3:2]==2'b11 ); // reserved state observed

  cover property ( $rose(ecfg_sw_reset) );
  cover property ( $rose(ecfg_reset) );
endmodule

// Bind to DUT
bind ecfg ecfg_sva #(.IDW(IDW)) ecfg_sva_i (
  .clk(clk),
  .hw_reset(hw_reset),
  .mi_access(mi_access),
  .mi_write(mi_write),
  .mi_addr(mi_addr),
  .mi_data_in(mi_data_in),
  .mi_data_out(mi_data_out),
  .mi_data_sel(mi_data_sel),
  .param_coreid(param_coreid),

  .ecfg_sw_reset(ecfg_sw_reset),
  .ecfg_reset(ecfg_reset),
  .ecfg_tx_enable(ecfg_tx_enable),
  .ecfg_tx_mmu_mode(ecfg_tx_mmu_mode),
  .ecfg_tx_gpio_mode(ecfg_tx_gpio_mode),
  .ecfg_tx_ctrl_mode(ecfg_tx_ctrl_mode),
  .ecfg_tx_clkdiv(ecfg_tx_clkdiv),
  .ecfg_rx_enable(ecfg_rx_enable),
  .ecfg_rx_mmu_mode(ecfg_rx_mmu_mode),
  .ecfg_rx_gpio_mode(ecfg_rx_gpio_mode),
  .ecfg_rx_loopback_mode(ecfg_rx_loopback_mode),
  .ecfg_cclk_en(ecfg_cclk_en),
  .ecfg_cclk_div(ecfg_cclk_div),
  .ecfg_cclk_pllcfg(ecfg_cclk_pllcfg),
  .ecfg_coreid(ecfg_coreid),
  .ecfg_gpio_dataout(ecfg_gpio_dataout),

  .ecfg_cfgtx_reg(ecfg_cfgtx_reg),
  .ecfg_cfgrx_reg(ecfg_cfgrx_reg),
  .ecfg_cfgclk_reg(ecfg_cfgclk_reg),
  .ecfg_coreid_reg(ecfg_coreid_reg),
  .ecfg_version_reg(ecfg_version_reg),
  .ecfg_reset_reg(ecfg_reset_reg),
  .ecfg_gpio_datain_reg(ecfg_gpio_datain_reg),
  .ecfg_gpio_dataout_reg(ecfg_gpio_dataout_reg),

  .ecfg_write(ecfg_write),
  .ecfg_read(ecfg_read),

  .ecfg_reset_match(ecfg_reset_match),
  .ecfg_cfgtx_match(ecfg_cfgtx_match),
  .ecfg_cfgrx_match(ecfg_cfgrx_match),
  .ecfg_cfgclk_match(ecfg_cfgclk_match),
  .ecfg_coreid_match(ecfg_coreid_match),
  .ecfg_version_match(ecfg_version_match),
  .ecfg_datain_match(ecfg_datain_match),
  .ecfg_dataout_match(ecfg_dataout_match),
  .ecfg_match(ecfg_match),

  .ecfg_reg_mux(ecfg_reg_mux),

  .ecfg_cfgtx_write(ecfg_cfgtx_write),
  .ecfg_cfgrx_write(ecfg_cfgrx_write),
  .ecfg_cfgclk_write(ecfg_cfgclk_write),
  .ecfg_coreid_write(ecfg_coreid_write),
  .ecfg_version_write(ecfg_version_write),
  .ecfg_datain_write(ecfg_datain_write),
  .ecfg_dataout_write(ecfg_dataout_write),
  .ecfg_reset_write(ecfg_reset_write),

  .ecfg_rx_monitor_mode(ecfg_rx_monitor_mode)
);