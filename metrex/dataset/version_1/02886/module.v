
module data_transfer(
  input CLK,
  input RESET_L,
  input writeRead_Regs_DATA,
  input [3:0] blockCount_Regs_DATA,
  input multipleData_Regs_DATA,
  input timeout_Enable_Regs_DATA,
  input [15:0] timeout_Reg_Regs_DATA,
  input new_DAT_DMA_DATA,
  input serial_Ready_Phy_DATA,
  output reg timeout_Phy_DATA,
  output reg complete_Phy_DATA,
  input ack_IN_Phy_DATA,
  input fifo_OK_FIFO_DATA,
  output reg ack_OUT_DATA_Phy,
  output reg [3:0] blocks_DATA_Phy,
  output reg idle_out_DATA_Phy,
  output reg multiple_DATA_Phy,
  output reg strobe_OUT_DATA_Phy,
  output reg [15:0] timeout_value_DATA_Phy,
  output reg transfer_complete_DATA_DMA,
  output reg writeReadPhysical_DATA_Phy
);

  reg [15:0] timeout_counter;
  reg [3:0] block_count;
  reg timeout_enable;
  reg multiple_data;
  reg write_read;

  always @(posedge CLK) begin
    if (RESET_L == 0) begin
      timeout_counter <= 0;
      block_count <= 0;
      timeout_enable <= 0;
      multiple_data <= 0;
      write_read <= 0;
      ack_OUT_DATA_Phy <= 0;
      blocks_DATA_Phy <= 0;
      idle_out_DATA_Phy <= 1;
      strobe_OUT_DATA_Phy <= 0;
      transfer_complete_DATA_DMA <= 0;
      writeReadPhysical_DATA_Phy <= 0;
      multiple_DATA_Phy <= 0;
    end else begin
      if (timeout_enable) begin
        if (timeout_counter < timeout_Reg_Regs_DATA) begin
          timeout_counter <= timeout_counter + 1;
        end else begin
          timeout_counter <= 0;
          timeout_enable <= 0;
          timeout_Phy_DATA <= 1'b1;
        end
      end
      if (new_DAT_DMA_DATA && serial_Ready_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA) begin
        timeout_counter <= 0;
        timeout_enable <= timeout_Enable_Regs_DATA;
        write_read <= writeRead_Regs_DATA;
        block_count <= blockCount_Regs_DATA;
        multiple_data <= multipleData_Regs_DATA;
        writeReadPhysical_DATA_Phy <= writeRead_Regs_DATA;
        blocks_DATA_Phy <= blockCount_Regs_DATA;
        idle_out_DATA_Phy <= 1'b0;
        strobe_OUT_DATA_Phy <= 1'b1;
        multiple_DATA_Phy <= 1'b1;
      end
      if (ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA) begin
        if (block_count == 0) begin
          transfer_complete_DATA_DMA <= 1'b1;
          idle_out_DATA_Phy <= 1'b1;
        end else begin
          block_count <= block_count - 1;
          blocks_DATA_Phy <= block_count - 1;
          strobe_OUT_DATA_Phy <= 1'b1;
        end
        multiple_DATA_Phy <= 1'b0;
      end
      if (fifo_OK_FIFO_DATA && !timeout_enable && !transfer_complete_DATA_DMA) begin
        ack_OUT_DATA_Phy <= 1'b1;
      end
      if (transfer_complete_DATA_DMA) begin
        complete_Phy_DATA <= 1'b1;
      end
      timeout_value_DATA_Phy <= timeout_counter;
    end
  end

endmodule