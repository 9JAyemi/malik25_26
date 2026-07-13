module fletcher_checksum (
  input [7:0] data,
  input rst,
  input clk,
  output reg [15:0] sum
);

  reg [7:0] byte_count;
  reg [15:0] sum_temp;
  reg [15:0] sum_prev;
  reg [15:0] sum_final;
  reg [1:0] state;

  always @(posedge clk) begin
    if (rst) begin
      state <= 2'b00;
      byte_count <= 8'd0;
      sum_temp <= 16'd0;
      sum_prev <= 16'd0;
      sum_final <= 16'd0;
      sum <= 16'd0;
    end
    else begin
      case (state)
        2'b00: begin // State 0: Add byte to sum_temp
          sum_temp <= sum_temp + data;
          byte_count <= byte_count + 8'd1;
          state <= 2'b01;
        end
        2'b01: begin // State 1: Add sum_temp to sum_prev
          sum_prev <= sum_prev + sum_temp;
          sum_temp <= 16'd0;
          if (byte_count == 8'd255) begin
            state <= 2'b10;
          end
          else begin
            state <= 2'b00;
          end
        end
        2'b10: begin // State 2: Truncate final sum and output
          sum_final <= sum_prev % 16'd255;
          sum <= sum_final;
          state <= 2'b11;
        end
        2'b11: begin // State 3: Check checksum
          if (sum_final == data) begin
            state <= 2'b00;
          end
          else begin
            state <= 2'b11;
          end
        end
      endcase
    end
  end

endmodule