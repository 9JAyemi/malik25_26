module LCD_driver (
  input clk,
  input [15:0] data,
  input [3:0] ctrl,
  output [15:0] addr,
  output busy
);

  reg [7:0] lcd_data;
  reg [3:0] lcd_ctrl;
  reg [3:0] state;
  reg [3:0] counter;
  reg busy_reg;

  parameter IDLE = 4'b0000;
  parameter WRITE_CMD = 4'b0001;
  parameter WRITE_DATA = 4'b0010;
  parameter CLEAR_SCREEN = 4'b0011;

  parameter LCD_BUSY_TIME = 4;

  always @(posedge clk) begin
    case(state)
      IDLE: begin
        if(ctrl == 4'b0001) begin
          lcd_ctrl <= 4'b0000;
          lcd_data <= 8'b00000001;
          state <= WRITE_CMD;
          counter <= 4'b0000;
          busy_reg <= 1'b1;
        end else if(ctrl == 4'b0010) begin
          lcd_ctrl <= 4'b0000;
          lcd_data <= data[7:0];
          state <= WRITE_DATA;
          counter <= 4'b0000;
          busy_reg <= 1'b1;
        end else if(ctrl == 4'b0011) begin
          lcd_ctrl <= 4'b0000;
          lcd_data <= 8'b00000001;
          state <= CLEAR_SCREEN;
          counter <= 4'b0000;
          busy_reg <= 1'b1;
        end else begin
          busy_reg <= 1'b0;
        end
      end

      WRITE_CMD: begin
        if(counter < LCD_BUSY_TIME) begin
          counter <= counter + 1;
          busy_reg <= 1'b1;
        end else begin
          lcd_ctrl <= 4'b0001;
          state <= IDLE;
          counter <= 4'b0000;
          busy_reg <= 1'b0;
        end
      end

      WRITE_DATA: begin
        if(counter < LCD_BUSY_TIME) begin
          counter <= counter + 1;
          busy_reg <= 1'b1;
        end else begin
          lcd_ctrl <= 4'b0001;
          lcd_data <= data[15:8];
          state <= IDLE;
          counter <= 4'b0000;
          busy_reg <= 1'b0;
        end
      end

      CLEAR_SCREEN: begin
        if(counter < LCD_BUSY_TIME) begin
          counter <= counter + 1;
          busy_reg <= 1'b1;
        end else begin
          lcd_ctrl <= 4'b0001;
          state <= IDLE;
          counter <= 4'b0000;
          busy_reg <= 1'b0;
        end
      end
    endcase
  end

  assign addr = 16'b0000000000000000;
  assign busy = busy_reg;

endmodule