
module NIOS_SYSTEMV3_LCD (
  // inputs:
  address,
  begintransfer,
  clk,
  read,
  reset_n,
  write,
  writedata,

  // outputs:
  LCD_E,
  LCD_RS,
  LCD_RW,
  LCD_data
);

  output LCD_E;
  output LCD_RS;
  output LCD_RW;
  output [7:0] LCD_data;
  input [1:0] address;
  input begintransfer;
  input clk;
  input read;
  input reset_n;
  input write;
  input [7:0] writedata;

  reg [7:0] LCD_data;

  assign LCD_RW = ~address[0];
  assign LCD_RS = address[1];

  reg LCD_E;
  always @(posedge clk or negedge reset_n)
    if (~reset_n)
      LCD_E <= 1'b0;
    else if (read | write)
      LCD_E <= 1'b1;
    else
      LCD_E <= 1'b0;

  always @(posedge clk or negedge reset_n)
  begin
    if (~reset_n)
      LCD_data <= 0;
    else if (write)
      LCD_data <= writedata;
  end

endmodule