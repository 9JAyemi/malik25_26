module lcd_driver (
  input clk,
  input rst,
  input [7:0] data,
  input rs,
  input rw,
  input en,
  output busy
);

  // Define constants for LCD commands
  parameter LCD_CLEAR_DISPLAY = 8'h01;
  parameter LCD_RETURN_HOME = 8'h02;
  parameter LCD_ENTRY_MODE_SET = 8'h04;
  parameter LCD_DISPLAY_CONTROL = 8'h08;
  parameter LCD_CURSOR_SHIFT = 8'h10;
  parameter LCD_FUNCTION_SET = 8'h20;
  parameter LCD_SET_CGRAM_ADDR = 8'h40;
  parameter LCD_SET_DDRAM_ADDR = 8'h80;

  // Define constants for LCD initialization
  parameter LCD_FUNCTION_SET_8BIT = 8'h30;
  parameter LCD_FUNCTION_SET_4BIT = 8'h20;
  parameter LCD_DISPLAY_CONTROL_ON = 8'h0C;
  parameter LCD_ENTRY_MODE_SET_INC = 8'h06;

  // Define internal signals
  reg [3:0] lcd_state = 0;
  reg busy = 0;
  reg [7:0] lcd_data = 0;
  reg [7:0] lcd_instruction = 0;
  reg [3:0] lcd_row = 0;
  reg [3:0] lcd_col = 0;

  // Define state machine
  always @(posedge clk, posedge rst) begin
    if (rst) begin
      lcd_state <= 0;
      busy <= 0;
      lcd_data <= 0;
      lcd_instruction <= 0;
      lcd_row <= 0;
      lcd_col <= 0;
    end else begin
      case (lcd_state)
        0: begin // Initialization
          lcd_instruction <= LCD_FUNCTION_SET_8BIT;
          lcd_state <= 1;
          busy <= 1;
        end
        1: begin
          lcd_instruction <= LCD_FUNCTION_SET_8BIT;
          lcd_state <= 2;
        end
        2: begin
          lcd_instruction <= LCD_FUNCTION_SET_8BIT;
          lcd_state <= 3;
        end
        3: begin
          lcd_instruction <= LCD_FUNCTION_SET_4BIT;
          lcd_state <= 4;
        end
        4: begin
          lcd_instruction <= LCD_DISPLAY_CONTROL_ON;
          lcd_state <= 5;
        end
        5: begin
          lcd_instruction <= LCD_ENTRY_MODE_SET_INC;
          lcd_state <= 6;
        end
        6: begin
          lcd_instruction <= LCD_CLEAR_DISPLAY;
          lcd_state <= 7;
        end
        7: begin
          lcd_instruction <= LCD_RETURN_HOME;
          lcd_state <= 8;
        end
        8: begin
          busy <= 0;
          lcd_state <= 9;
        end
        9: begin // Write data or instruction
          if (en && !busy) begin
            if (rs) begin // Data
              lcd_instruction <= LCD_SET_DDRAM_ADDR | ((lcd_row << 6) + lcd_col);
              lcd_data <= data;
            end else begin // Instruction
              lcd_instruction <= data;
            end
            busy <= 1;
            lcd_state <= 10;
          end
        end
        10: begin // Send data or instruction
          if (en) begin
            lcd_instruction <= lcd_instruction | 4'b0001;
            lcd_state <= 11;
          end
        end
        11: begin // Wait for busy signal to clear
          if (!en) begin
            busy <= 1;
            lcd_state <= 12;
          end
        end
        12: begin // Send data or instruction
          if (en) begin
            lcd_instruction <= lcd_instruction & 4'b1110;
            if (rs) begin // Data
              lcd_data <= 0;
            end
            busy <= 0;
            lcd_state <= 9;
            if (lcd_col == 15) begin
              if (lcd_row == 0) begin
                lcd_row <= 1;
              end else begin
                lcd_row <= 0;
              end
              lcd_col <= 0;
            end else begin
              lcd_col <= lcd_col + 1;
            end
          end
        end
      endcase
    end
  end

endmodule