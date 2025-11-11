module lcd_driver (
  input clk,
  input reset,
  input enable,
  input in_cmd,
  input [7:0] in_data,
  output [7:0] lcd_pins,
  output rs,
  output rw,
  output backlight
);

  // Define internal signals
  reg [7:0] lcd_data;
  reg lcd_rs;
  reg lcd_rw;
  reg lcd_backlight;
  reg lcd_enable;

  // Define constants for LCD commands
  parameter LCD_CLEAR_DISPLAY = 8'h01;
  parameter LCD_RETURN_HOME = 8'h02;
  parameter LCD_ENTRY_MODE_SET = 8'h04;
  parameter LCD_DISPLAY_ON_OFF_CONTROL = 8'h08;
  parameter LCD_CURSOR_DISPLAY_SHIFT = 8'h10;
  parameter LCD_FUNCTION_SET = 8'h20;
  parameter LCD_SET_CGRAM_ADDRESS = 8'h40;
  parameter LCD_SET_DDRAM_ADDRESS = 8'h80;

  // Define state variables
  reg [2:0] state;
  parameter STATE_IDLE = 3'b000;
  parameter STATE_WAIT_ENABLE = 3'b001;
  parameter STATE_SEND_COMMAND = 3'b010;
  parameter STATE_SEND_DATA = 3'b011;

  // Initialize internal signals and state variables
  initial begin
    lcd_data <= 8'h00;
    lcd_rs <= 1'b0;
    lcd_rw <= 1'b0;
    lcd_backlight <= 1'b0;
    lcd_enable <= 1'b0;
    state <= STATE_IDLE;
  end

  // Define state machine
  always @(posedge clk) begin
    case (state)
      STATE_IDLE: begin
        if (reset) begin
          state <= STATE_IDLE;
        end else if (enable) begin
          state <= STATE_WAIT_ENABLE;
        end
      end
      STATE_WAIT_ENABLE: begin
        if (reset) begin
          state <= STATE_IDLE;
        end else if (!enable) begin
          state <= STATE_IDLE;
        end else if (in_cmd) begin
          state <= STATE_SEND_COMMAND;
        end else begin
          state <= STATE_SEND_DATA;
        end
      end
      STATE_SEND_COMMAND: begin
        lcd_data <= in_data;
        lcd_rs <= 1'b0;
        lcd_rw <= 1'b0;
        lcd_backlight <= 1'b1;
        lcd_enable <= 1'b1;
        state <= STATE_IDLE;
      end
      STATE_SEND_DATA: begin
        lcd_data <= in_data;
        lcd_rs <= 1'b1;
        lcd_rw <= 1'b0;
        lcd_backlight <= 1'b1;
        lcd_enable <= 1'b1;
        state <= STATE_IDLE;
      end
    endcase
  end

  // Assign outputs
  assign lcd_pins = lcd_data;
  assign rs = lcd_rs;
  assign rw = lcd_rw;
  assign backlight = lcd_backlight;

endmodule