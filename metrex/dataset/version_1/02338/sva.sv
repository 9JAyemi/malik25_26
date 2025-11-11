// SVA for dcr_if. Bind this to the DUT.
// Focus: protocol/handshake, decode, register reset/update, read-data return path, and mux behavior.

module dcr_if_sva #(
  parameter [0:9]  C_DCR_BASE_ADDR           = 10'b00_0000_0000,
  parameter [0:30] C_DEFAULT_TFT_BASE_ADDR   = 31'b0,
  parameter        C_DPS_INIT                = 1'b1,
  parameter        C_ON_INIT                 = 1'b1
)(
  input         clk,
  input         rst,
  input  [0:9]  DCR_ABus,
  input  [0:31] DCR_DBusIn,
  input         DCR_Read,
  input         DCR_Write,
  input         DCR_Ack,
  input  [0:31] DCR_DBusOut,
  input  [0:10] tft_base_addr,
  input         tft_dps_reg,
  input         tft_on_reg
);

  default clocking cb @(posedge clk); endclocking

  // Sampling guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Local decodes that mirror DUT
  wire dcr_addr_hit = (DCR_ABus[0:8] == C_DCR_BASE_ADDR[0:8]);
  wire we_base  = DCR_Write & ~DCR_Ack & dcr_addr_hit & (DCR_ABus[9] == 1'b0);
  wire we_ctrl  = DCR_Write & ~DCR_Ack & dcr_addr_hit & (DCR_ABus[9] == 1'b1);
  wire rd_fire  = DCR_Read  & ~DCR_Ack & dcr_addr_hit;

  // 1) Handshake/Ack must reflect prior-cycle cmd+hit (registered)
  //    DCR_Ack <= (DCR_Read|DCR_Write) & dcr_addr_hit;
  assert property (past_valid |-> DCR_Ack == $past((DCR_Read|DCR_Write) & dcr_addr_hit));

  // 2) Reset values (registered on rst cycle)
  assert property (rst |=> tft_base_addr == C_DEFAULT_TFT_BASE_ADDR[31:21]);
  assert property (rst |=> tft_dps_reg == C_DPS_INIT && tft_on_reg == C_ON_INIT);

  // 3) Writes update correct fields next cycle
  assert property (past_valid && we_base |=> tft_base_addr == $past(DCR_DBusIn[0:10]));
  assert property (past_valid && we_ctrl |=> tft_dps_reg  == $past(DCR_DBusIn[30]));
  assert property (past_valid && we_ctrl |=> tft_on_reg   == $past(DCR_DBusIn[31]));

  // 4) Registers hold when not written (outside reset)
  assert property (past_valid && !rst && !we_base |=> tft_base_addr == $past(tft_base_addr));
  assert property (past_valid && !rst && !we_ctrl |=> {tft_dps_reg,tft_on_reg} == $past({tft_dps_reg,tft_on_reg}));

  // 5) Read returns the correct data word next cycle (through read_data/dcr_read_access path)
  // read_data captures current reg values; next cycle mux selects read_data
  assert property (past_valid && rd_fire |=> DCR_DBusOut ==
                   ($past(DCR_ABus[9]) == 1'b0 ? {$past(tft_base_addr), 21'b0}
                                               : {30'b0, $past(tft_dps_reg), $past(tft_on_reg)}));

  // 6) When no read was requested in the prior cycle, DCR_DBusOut should pass through DCR_DBusIn
  //    (since dcr_read_access is the registered DCR_Read&hit)
  assert property (past_valid && !$past(DCR_Read & dcr_addr_hit) |-> DCR_DBusOut == DCR_DBusIn);

  // 7) Outputs should not be X/Z after first sampled cycle (and outside of active rst for regs)
  assert property (past_valid |-> !$isunknown(DCR_Ack));
  assert property (past_valid && !rst |-> !$isunknown({tft_base_addr,tft_dps_reg,tft_on_reg}));
  assert property (past_valid |-> !$isunknown(DCR_DBusOut));

  // 8) Coverage: exercise key transactions
  cover property (past_valid && (DCR_Read|DCR_Write) && dcr_addr_hit ##1 DCR_Ack);           // ack toggles
  cover property (past_valid && we_base);                                                    // base write
  cover property (past_valid && we_ctrl);                                                    // ctrl write
  cover property (past_valid && rd_fire && (DCR_ABus[9]==1'b0));                             // base read
  cover property (past_valid && rd_fire && (DCR_ABus[9]==1'b1));                             // ctrl read
  cover property (past_valid && !$past(DCR_Read & dcr_addr_hit) && (DCR_DBusOut == DCR_DBusIn)); // passthrough

endmodule

bind dcr_if dcr_if_sva #(
  .C_DCR_BASE_ADDR(C_DCR_BASE_ADDR),
  .C_DEFAULT_TFT_BASE_ADDR(C_DEFAULT_TFT_BASE_ADDR),
  .C_DPS_INIT(C_DPS_INIT),
  .C_ON_INIT(C_ON_INIT)
) dcr_if_sva_i (
  .clk(clk),
  .rst(rst),
  .DCR_ABus(DCR_ABus),
  .DCR_DBusIn(DCR_DBusIn),
  .DCR_Read(DCR_Read),
  .DCR_Write(DCR_Write),
  .DCR_Ack(DCR_Ack),
  .DCR_DBusOut(DCR_DBusOut),
  .tft_base_addr(tft_base_addr),
  .tft_dps_reg(tft_dps_reg),
  .tft_on_reg(tft_on_reg)
);