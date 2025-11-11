
module fifo_buffer (
  input in0, 
  input rd_clk, 
  input [2:0] g7serrst, 
  output reg out
);

  reg Q_reg;
  wire in0_sync;
  reg rd_rst_asreg_reg;

  fifo_bt_txd_synchronizer_ff sync (
    .in0(in0),
    .rd_clk(rd_clk),
    .out(in0_sync),
    .rd_rst_asreg_reg(rd_rst_asreg_reg)
  );

  always @ (posedge rd_clk or negedge g7serrst[0]) begin
    if (~g7serrst[0]) begin
      Q_reg <= 1'b0;
      rd_rst_asreg_reg <= 1'b0;
    end else begin
      Q_reg <= in0_sync;
      rd_rst_asreg_reg <= ~Q_reg & in0_sync;
    end
  end

  always @ (posedge rd_clk) begin
    out <= Q_reg;
  end

endmodule
module fifo_bt_txd_synchronizer_ff (
  input in0, 
  input rd_clk, 
  output reg out, 
  input rd_rst_asreg_reg
);

  reg Q_reg;
  reg [0:0] in0_sync;

  always @ (posedge rd_clk) begin
    in0_sync <= in0;
  end

  always @ (posedge rd_clk or negedge rd_rst_asreg_reg) begin
    if (~rd_rst_asreg_reg) begin
      Q_reg <= 1'b0;
    end else begin
      Q_reg <= in0_sync;
    end
  end

  always @ (posedge rd_clk) begin
    out <= Q_reg;
  end

endmodule