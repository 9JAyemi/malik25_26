// SVA for spi_engine_offload
// Concise, high-value checks; includes coverage and minimal assumptions for async case.

module spi_engine_offload_sva #(
  parameter SPI_CLK_ASYNC = 0,
  parameter CMD_MEM_ADDR_WIDTH = 4,
  parameter SDO_MEM_ADDR_WIDTH = 4
)(
  input  logic                   ctrl_clk,
  input  logic                   spi_clk,
  input  logic                   spi_resetn,

  // CTRL domain
  input  logic                   ctrl_mem_reset,
  input  logic                   ctrl_enable,
  input  logic                   ctrl_cmd_wr_en,
  input  logic                   ctrl_sdo_wr_en,
  input  logic [CMD_MEM_ADDR_WIDTH-1:0] ctrl_cmd_wr_addr,
  input  logic [SDO_MEM_ADDR_WIDTH-1:0] ctrl_sdo_wr_addr,

  // SPI domain interfaces
  input  logic                   trigger,
  input  logic                   cmd_ready,
  input  logic                   sdo_data_ready,
  input  logic                   sdi_data_valid,
  input  logic                   offload_sdi_ready,
  input  logic [7:0]             sdi_data,

  // DUT internals/outputs
  input  logic                   spi_active,
  input  logic [CMD_MEM_ADDR_WIDTH-1:0] spi_cmd_rd_addr,
  input  logic [SDO_MEM_ADDR_WIDTH-1:0] spi_sdo_rd_addr,
  input  logic [15:0]            cmd,
  input  logic [7:0]             sdo_data,
  input  logic                   cmd_valid,
  input  logic                   sdo_data_valid,
  input  logic                   offload_sdi_valid,
  input  logic                   sdi_data_ready,
  input  logic [7:0]             offload_sdi_data,
  input  logic                   sync_ready,
  input  logic                   spi_enable,
  input  logic                   ctrl_enabled
);

  // Basic signal equivalences
  assert property (@(posedge spi_clk) disable iff(!spi_resetn) cmd_valid == spi_active);
  assert property (@(posedge spi_clk) disable iff(!spi_resetn) sdo_data_valid == spi_active);

  // Pass-through SDI offload
  assert property (@(posedge spi_clk)) offload_sdi_valid == sdi_data_valid;
  assert property (@(posedge spi_clk)) sdi_data_ready    == offload_sdi_ready;
  assert property (@(posedge spi_clk)) offload_sdi_data  == sdi_data;

  // sync_ready is constant 1
  assert property (@(posedge spi_clk)) sync_ready;

  // spi_active control: rise/fall causes (SYNC case only, to avoid CDC false fails)
  if (SPI_CLK_ASYNC == 0) begin
    // Enter active only on trigger && enable
    assert property (@(posedge spi_clk) disable iff(!spi_resetn)
      $rose(spi_active) |-> $past(!spi_active && trigger && spi_enable));

    // Exit active only when end condition is met in same cycle
    assert property (@(posedge spi_clk) disable iff(!spi_resetn)
      $fell(spi_active) |-> $past(spi_active && cmd_ready &&
                                  ($past(spi_cmd_rd_addr)+1 == $past(ctrl_cmd_wr_addr))));

    // End condition implies deactivation next cycle
    assert property (@(posedge spi_clk) disable iff(!spi_resetn)
      spi_active && cmd_ready && (spi_cmd_rd_addr+1 == ctrl_cmd_wr_addr) |=> !spi_active);

    // While active and not at end condition, remain active
    assert property (@(posedge spi_clk) disable iff(!spi_resetn)
      spi_active && !(cmd_ready && (spi_cmd_rd_addr+1 == ctrl_cmd_wr_addr)) |=> spi_active);

    // In sync mode, enable relationships
    assert property (@(posedge spi_clk)) spi_enable == ctrl_enable;
    assert property (@(posedge spi_clk)) ctrl_enabled == (ctrl_enable || spi_active);
  end

  // Minimal environment assumption for ASYNC mode: freeze ctrl_cmd_wr_addr during active
  // (prevents CDC false failures around end-of-transfer equality)
  if (SPI_CLK_ASYNC != 0) begin
    assume property (@(posedge spi_clk) disable iff(!spi_resetn)
      spi_active |-> $stable(ctrl_cmd_wr_addr));
  end

  // Read-side command address behavior
  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    !spi_active |=> (spi_cmd_rd_addr == '0));

  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    spi_active &&  cmd_ready |=> spi_cmd_rd_addr == $past(spi_cmd_rd_addr)+1);

  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    spi_active && !cmd_ready |=> $stable(spi_cmd_rd_addr));

  // Read-side SDO address behavior
  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    !spi_active |=> (spi_sdo_rd_addr == '0));

  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    spi_active &&  sdo_data_ready |=> spi_sdo_rd_addr == $past(spi_sdo_rd_addr)+1);

  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    spi_active && !sdo_data_ready |=> $stable(spi_sdo_rd_addr));

  // CTRL-side write address behavior
  assert property (@(posedge ctrl_clk)
    ctrl_mem_reset |=> (ctrl_cmd_wr_addr == '0));

  assert property (@(posedge ctrl_clk)
    ctrl_mem_reset |=> (ctrl_sdo_wr_addr == '0));

  assert property (@(posedge ctrl_clk)
    !ctrl_mem_reset && ctrl_cmd_wr_en |=> ctrl_cmd_wr_addr == $past(ctrl_cmd_wr_addr)+1);

  assert property (@(posedge ctrl_clk)
    !ctrl_mem_reset && !ctrl_cmd_wr_en |=> $stable(ctrl_cmd_wr_addr));

  assert property (@(posedge ctrl_clk)
    !ctrl_mem_reset && ctrl_sdo_wr_en |=> ctrl_sdo_wr_addr == $past(ctrl_sdo_wr_addr)+1);

  assert property (@(posedge ctrl_clk)
    !ctrl_mem_reset && !ctrl_sdo_wr_en |=> $stable(ctrl_sdo_wr_addr));

  // No-X on key outputs (when out of reset)
  assert property (@(posedge spi_clk) disable iff(!spi_resetn)
    !$isunknown({cmd_valid, sdo_data_valid, cmd, sdo_data,
                 offload_sdi_valid, sdi_data_ready, offload_sdi_data, sync_ready}));

  // Coverage: a complete offload transaction (SYNC case for robustness)
  if (SPI_CLK_ASYNC == 0) begin
    cover property (@(posedge spi_clk) disable iff(!spi_resetn)
      !spi_active ##1 (trigger && spi_enable)
      ##1 spi_active [*1:$]
      ##1 (cmd_ready && (spi_cmd_rd_addr+1 == ctrl_cmd_wr_addr))
      ##1 !spi_active);

    // Coverage: multiple SDO beats while active
    cover property (@(posedge spi_clk) disable iff(!spi_resetn)
      spi_active ##1 sdo_data_ready [*3]);

    // Coverage: SDI pass-through handshake
    cover property (@(posedge spi_clk) disable iff(!spi_resetn)
      sdi_data_valid && offload_sdi_ready ##1 sdi_data_ready);
  end

endmodule

// Bind into DUT
bind spi_engine_offload spi_engine_offload_sva #(
  .SPI_CLK_ASYNC(SPI_CLK_ASYNC),
  .CMD_MEM_ADDR_WIDTH(CMD_MEM_ADDR_WIDTH),
  .SDO_MEM_ADDR_WIDTH(SDO_MEM_ADDR_WIDTH)
) u_spi_engine_offload_sva (
  .ctrl_clk(ctrl_clk),
  .spi_clk(spi_clk),
  .spi_resetn(spi_resetn),

  .ctrl_mem_reset(ctrl_mem_reset),
  .ctrl_enable(ctrl_enable),
  .ctrl_cmd_wr_en(ctrl_cmd_wr_en),
  .ctrl_sdo_wr_en(ctrl_sdo_wr_en),
  .ctrl_cmd_wr_addr(ctrl_cmd_wr_addr),
  .ctrl_sdo_wr_addr(ctrl_sdo_wr_addr),

  .trigger(trigger),
  .cmd_ready(cmd_ready),
  .sdo_data_ready(sdo_data_ready),
  .sdi_data_valid(sdi_data_valid),
  .offload_sdi_ready(offload_sdi_ready),
  .sdi_data(sdi_data),

  .spi_active(spi_active),
  .spi_cmd_rd_addr(spi_cmd_rd_addr),
  .spi_sdo_rd_addr(spi_sdo_rd_addr),
  .cmd(cmd),
  .sdo_data(sdo_data),
  .cmd_valid(cmd_valid),
  .sdo_data_valid(sdo_data_valid),
  .offload_sdi_valid(offload_sdi_valid),
  .sdi_data_ready(sdi_data_ready),
  .offload_sdi_data(offload_sdi_data),
  .sync_ready(sync_ready),
  .spi_enable(spi_enable),
  .ctrl_enabled(ctrl_enabled)
);