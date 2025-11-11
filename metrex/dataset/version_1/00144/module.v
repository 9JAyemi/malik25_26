module lcd_driver #(
  parameter n = 8, // number of data signals
  parameter m = 16 // number of output signals (for a 16x2 LCD display)
) (
  input [n-1:0] data,
  input clk,
  input rst,
  output reg [m-1:0] out
);


// Define ASCII code for characters and numbers
parameter ASCII_A = 8'h41;
parameter ASCII_0 = 8'h30;

// Define commands for the LCD panel
parameter CMD_CLEAR_DISPLAY = 4'b0001;
parameter CMD_RETURN_HOME = 4'b0010;
parameter CMD_ENTRY_MODE_SET = 4'b0110;
parameter CMD_DISPLAY_ON_OFF_CONTROL = 4'b1000;
parameter CMD_FUNCTION_SET = 4'b0010;

// Define internal signals
reg [3:0] data_bus;
reg [3:0] cmd_bus;
reg [3:0] lcd_state;
reg [3:0] lcd_row;
reg [3:0] lcd_col;

// Define state machine states
parameter STATE_INIT = 4'b0000;
parameter STATE_CLEAR_DISPLAY = 4'b0001;
parameter STATE_RETURN_HOME = 4'b0010;
parameter STATE_ENTRY_MODE_SET = 4'b0011;
parameter STATE_DISPLAY_ON_OFF_CONTROL = 4'b0100;
parameter STATE_FUNCTION_SET = 4'b0101;
parameter STATE_WRITE_DATA = 4'b0110;
parameter STATE_WRITE_COMMAND = 4'b0111;

// Define state machine transitions
always @(posedge clk) begin
  if (rst) begin
    lcd_state <= STATE_INIT;
    lcd_row <= 4'b0000;
    lcd_col <= 4'b0000;
  end else begin
    case (lcd_state)
      STATE_INIT: begin
        cmd_bus <= CMD_FUNCTION_SET;
        lcd_state <= STATE_FUNCTION_SET;
      end
      STATE_CLEAR_DISPLAY: begin
        cmd_bus <= CMD_CLEAR_DISPLAY;
        lcd_state <= STATE_FUNCTION_SET;
      end
      STATE_RETURN_HOME: begin
        cmd_bus <= CMD_RETURN_HOME;
        lcd_state <= STATE_FUNCTION_SET;
      end
      STATE_ENTRY_MODE_SET: begin
        cmd_bus <= CMD_ENTRY_MODE_SET;
        lcd_state <= STATE_FUNCTION_SET;
      end
      STATE_DISPLAY_ON_OFF_CONTROL: begin
        cmd_bus <= CMD_DISPLAY_ON_OFF_CONTROL;
        lcd_state <= STATE_FUNCTION_SET;
      end
      STATE_FUNCTION_SET: begin
        cmd_bus <= CMD_FUNCTION_SET;
        lcd_state <= STATE_WRITE_COMMAND;
      end
      STATE_WRITE_DATA: begin
        data_bus <= data[7:4];
        lcd_state <= STATE_WRITE_COMMAND;
      end
      STATE_WRITE_COMMAND: begin
        out <= {cmd_bus, data_bus}; // Fix the syntax error here
        lcd_col <= lcd_col + 1;
        if (lcd_col == 4'b0100) begin
          lcd_col <= 4'b0000;
          lcd_row <= lcd_row + 1;
          if (lcd_row == 4'b0010) begin
            lcd_row <= 4'b0000;
          end
        end
        if (lcd_row == 4'b0000 && lcd_col == 4'b0000) begin
          lcd_state <= STATE_CLEAR_DISPLAY;
        end else begin
          lcd_state <= STATE_WRITE_DATA;
        end
      end
    endcase
  end
end

endmodule