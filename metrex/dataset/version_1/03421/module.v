module uart_transmitter(
  input clk, reset, din, baud_clk,
  output tx
);

reg [7:0] shift_reg;
reg tx_busy;
reg tx;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    shift_reg <= 8'b0;
    tx_busy <= 1'b0;
    tx <= 1'b1;
  end else begin
    if (baud_clk) begin
      if (!tx_busy) begin
        shift_reg <= din;
        tx_busy <= 1'b1;
      end else begin
        shift_reg <= {shift_reg[6:0], 1'b0};
        if (shift_reg == 8'b0) begin
          tx_busy <= 1'b0;
        end
      end
      tx <= shift_reg[7];
    end
  end
end

endmodule

module uart_receiver(
  input clk, reset, rx, baud_clk,
  output dout
);

reg [7:0] shift_reg;
reg rx_busy;
wire dout;

assign dout = shift_reg[7];

always @(posedge clk or posedge reset) begin
  if (reset) begin
    shift_reg <= 8'b0;
    rx_busy <= 1'b0;
  end else begin
    if (baud_clk) begin
      if (!rx_busy) begin
        if (rx == 1'b0) begin
          rx_busy <= 1'b1;
        end
      end else begin
        shift_reg <= {shift_reg[6:0], rx};
        if (shift_reg == 8'b0) begin
          rx_busy <= 1'b0;
        end
      end
    end
  end
end

endmodule