
module lin_transmitter (
  input clk,
  input rst,
  input [7:0] tx_data,
  input tx_en,
  output tx
);

  reg [3:0] state;
  reg [7:0] id;
  reg [7:0] data;
  reg parity;
  reg [3:0] bit_count;
  reg start_bit;
  reg stop_bit;
  reg tx_data_reg;
  integer i;
  
  assign tx = tx_data_reg;
  
  always @(posedge clk) begin
    if (rst) begin
      state <= 4'b0000;
      id <= 8'b00000000;
      data <= 8'b00000000;
      bit_count <= 4'b0000;
      start_bit <= 1'b0;
      stop_bit <= 1'b0;
      tx_data_reg <= 1'b0;
      parity <= 1'b0;
    end else begin
      case (state)
        4'b0000: begin // IDLE state
          if (tx_en) begin
            state <= 4'b0001;
            start_bit <= 1'b1;
            id <= tx_data;
            data <= {tx_data[6:0], parity};
          end
        end
        4'b0001: begin // SYNC BREAK state
          if (bit_count == 4'b0000) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
          end else if (bit_count < 4'b0010) begin
            tx_data_reg <= 1'b1;
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b0010) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b0011) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
            state <= 4'b0010;
          end
        end
        4'b0010: begin // SYNC FIELD state
          if (bit_count == 4'b0000) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
          end else if (bit_count < 4'b1000) begin
            tx_data_reg <= id[bit_count-4];
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b1000) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
            state <= 4'b0011;
          end
        end
        4'b0011: begin // DATA FIELD state
          if (bit_count == 4'b0000) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
          end else if (bit_count < 4'b1000) begin
            tx_data_reg <= data[bit_count-1];
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b1000) begin
            tx_data_reg <= parity;
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b1001) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
            state <= 4'b0100;
          end
        end
        4'b0100: begin // STOP BITS state
          if (bit_count == 4'b0000) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
          end else if (bit_count < 4'b0010) begin
            tx_data_reg <= 1'b1;
            bit_count <= bit_count + 1;
          end else if (bit_count == 4'b0010) begin
            tx_data_reg <= 1'b0;
            bit_count <= bit_count + 1;
            state <= 4'b0000;
          end
        end
      endcase
    end
    
    if (start_bit) begin
      parity <= 1'b0;
      for (i = 0; i < 8; i = i + 1) begin
        parity <= parity ^ id[i];
      end
      for (i = 0; i < 8; i = i + 1) begin
        parity <= parity ^ data[i];
      end
      start_bit <= 1'b0;
    end
    
    if (stop_bit) begin
      bit_count <= 4'b0000;
      stop_bit <= 1'b0;
    end
    
    if (bit_count == 4'b1001) begin
      stop_bit <= 1'b1;
    end
    
    if (state == 4'b0010 || state == 4'b0011 || state == 4'b0100) begin
      tx_data_reg <= 1'b0;
    end else begin
      tx_data_reg <= 1'b1;
    end
    
  end
  
endmodule