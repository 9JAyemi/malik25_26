// SVA for SPI_IF_accel
// Bind this file to the DUT:
// bind SPI_IF_accel SPI_IF_accel_sva sva();

module SPI_IF_accel_sva;

  // Use DUT clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset defaults (must check during reset)
  property p_reset_defaults;
    @(posedge clk) disable iff (1'b0)
      rst |-> (SPI_SS_a==1'b1 && SPI_CK_a==1'b1 && SPI_DO_a==1'b0 && busy==1'b0 && mpu_rd_data==8'h00);
  endproperty
  assert property (p_reset_defaults);

  // No X on key outputs
  assert property (!$isunknown({SPI_SS_a,SPI_CK_a,SPI_DO_a,busy,mpu_rd_data}));

  // Start only when idle
  assert property ($rose(start) |-> (SPIstate==8'd0 && !busy));

  // Busy holds until back to idle with start low
  assert property ($rose(busy) |-> (busy until_with (SPIstate==8'd0 && !start)));

  // SS by state
  assert property ((SPIstate inside {8'd1,8'd3,8'd4,8'd5}) |-> (SPI_SS_a==1'b0));
  assert property ((SPIstate inside {8'd0,8'd6,8'd7}) |-> (SPI_SS_a==1'b1));

  // When SS high, CK must be high
  assert property (SPI_SS_a |-> (SPI_CK_a==1'b1));

  // When SS low, CK only changes on halfCLKpassed
  assert property ((SPI_SS_a==1'b0 && !halfCLKpassed) |-> $stable(SPI_CK_a));

  // Counter/MPUclk behavior
  assert property ((start) |=> (counter==12'd0 && MPUclk==1'b1));
  assert property ((!start && halfCLKpassed) |=> (counter==12'd0 && MPUclk!=$past(MPUclk)));
  assert property ((!start && !halfCLKpassed) |=> (counter==$past(counter)+12'd1));

  // DO timing: stable between halfCLKpassed while shifting
  assert property ((SPI_SS_a==1'b0 && (SPIstate==8'd3 || SPIstate==8'd5) && !halfCLKpassed) |-> $stable(SPI_DO_a));

  // DO forced low in idle/stop
  assert property ((SPIstate inside {8'd0,8'd6}) |-> (SPI_DO_a==1'b0));

  // i/j reset when idle
  assert property ((SPIstate==8'd0) |-> (i==5'd16 && j==5'd17));

  // Command/address bit mapping in state 3 (sampled next cycle)
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd16) |-> (SPI_DO_a==$past(mpu_rd_wr_sel)));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd14) |-> (SPI_DO_a==$past(mpu_address[6])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd12) |-> (SPI_DO_a==$past(mpu_address[5])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd10) |-> (SPI_DO_a==$past(mpu_address[4])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd8)  |-> (SPI_DO_a==$past(mpu_address[3])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd6)  |-> (SPI_DO_a==$past(mpu_address[2])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd4)  |-> (SPI_DO_a==$past(mpu_address[1])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd2)  |-> (SPI_DO_a==$past(mpu_address[0])));
  assert property ($past(SPIstate==8'd3 && halfCLKpassed && i==5'd0)  |-> (SPI_DO_a==1'b0));

  // Write data bit mapping in state 5 (sampled next cycle)
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd16) |-> (SPI_DO_a==$past(mpu_wr_data[7])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd14) |-> (SPI_DO_a==$past(mpu_wr_data[6])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd12) |-> (SPI_DO_a==$past(mpu_wr_data[5])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd10) |-> (SPI_DO_a==$past(mpu_wr_data[4])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd8)  |-> (SPI_DO_a==$past(mpu_wr_data[3])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd6)  |-> (SPI_DO_a==$past(mpu_wr_data[2])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd4)  |-> (SPI_DO_a==$past(mpu_wr_data[1])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd2)  |-> (SPI_DO_a==$past(mpu_wr_data[0])));
  assert property ($past(SPIstate==8'd5 && halfCLKpassed && j==5'd0)  |-> (SPI_DO_a==1'b0));

  // Read data capture mapping in state 4 (sampled into mpu_rd_data next cycle)
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd16) |-> (mpu_rd_data[7]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd14) |-> (mpu_rd_data[6]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd12) |-> (mpu_rd_data[5]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd10) |-> (mpu_rd_data[4]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd8)  |-> (mpu_rd_data[3]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd6)  |-> (mpu_rd_data[2]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd4)  |-> (mpu_rd_data[1]==$past(SPI_DI_a)));
  assert property ($past(SPIstate==8'd4 && halfCLKpassed && j==5'd2)  |-> (mpu_rd_data[0]==$past(SPI_DI_a)));

  // mpu_rd_data changes only during read-capture halfCLKpassed
  assert property (!(SPIstate==8'd4 && halfCLKpassed) |-> $stable(mpu_rd_data));

  // Liveness: transaction completes
  assert property ($rose(start) |-> ##[1:2000] (SPIstate==8'd0 && !busy));

  // Coverage
  cover property ($rose(start) && mpu_rd_wr_sel ##[1:$] (SPIstate==8'd0 && !busy));
  cover property ($rose(start) && !mpu_rd_wr_sel ##[1:$] (SPIstate==8'd0 && !busy));
  cover property ($rose(start) ##[1:$] (i==5'd0) ##[1:$] (j==5'd0));

endmodule