
module spi_master (
  input clk,
  input rst,
  input mosi,
  input cs,
  input sck_div,
  output reg miso
);

reg [7:0] shift_reg;
reg [2:0] bit_counter;
reg sck;
reg cs_n;

always @(posedge clk) begin
  if (rst) begin
    shift_reg <= 8'h00;
    bit_counter <= 3'd0;
    sck <= 1'b0;
    cs_n <= 1'b1;
    miso <= 1'b0;
  end else begin
    if (!cs_n && sck) begin
      shift_reg <= {mosi, shift_reg[7:1]};
      bit_counter <= bit_counter + 1;
      if (bit_counter == 3'd7) begin
        miso <= shift_reg[0];
        bit_counter <= 3'd0;
      end
    end
    sck <= ~sck; // Toggle the clock
    if (sck) begin
      cs_n <= cs;
    end
  end
end

endmodule

module spi_slave (
  input clk,
  input rst,
  input miso,
  input cs,
  input sck_div,
  output reg mosi
);

reg [7:0] shift_reg;
reg [2:0] bit_counter;
reg sck;
reg cs_n;

always @(posedge clk) begin
  if (rst) begin
    shift_reg <= 8'h00;
    bit_counter <= 3'd0;
    sck <= 1'b0;
    cs_n <= 1'b1;
    mosi <= 1'b0;
  end else begin
    sck <= ~sck; // Toggle the clock
    if (sck) begin
      cs_n <= cs;
      if (!cs_n) begin
        shift_reg <= {shift_reg[6:0], miso};
        bit_counter <= bit_counter + 1;
        if (bit_counter == 3'd7) begin
          mosi <= shift_reg[7];
          bit_counter <= 3'd0;
        end
      end
    end
  end
end

endmodule
