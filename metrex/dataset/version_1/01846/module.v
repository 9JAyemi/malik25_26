module vga_sync_generator(
  input clk,
  output vga_h_sync,
  output vga_v_sync,
  output inDisplayArea,
  output reg [10:0] CounterX,
  output reg [10:0] CounterY
);

  // VGA display parameters
  parameter WIDTH = 800;
  parameter HEIGHT = 600;
  parameter COUNT_DOTS = 1056;
  parameter COUNT_LINES = 625;
  
  parameter H_FRONT_PORCH = 16;
  parameter H_SYNC_PULSE = 80;
  parameter H_BACK_PORCH = 160;
  
  parameter V_FRONT_PORCH = 1;
  parameter V_SYNC_PULSE = 3;
  parameter V_BACK_PORCH = 21;
  
  // Horizontal and vertical sync signals
  reg vga_HS, vga_VS;
  
  // Counter max values
  wire CounterXmaxed = (CounterX == COUNT_DOTS);
  wire CounterYmaxed = (CounterY == COUNT_LINES);
  
  // Increment counters
  always @(posedge clk) begin
    if (CounterXmaxed) begin
      CounterX <= 0;
      if (CounterYmaxed)
        CounterY <= 0;
      else
        CounterY <= CounterY + 1;
    end
    else
      CounterX <= CounterX + 1;
  end
  
  // Generate sync signals
  always @(posedge clk) begin
    vga_HS <= (CounterX >= (WIDTH + H_FRONT_PORCH) && CounterX < (WIDTH + H_FRONT_PORCH + H_SYNC_PULSE)); 
    vga_VS <= (CounterY >= (HEIGHT + V_FRONT_PORCH) && CounterY < (HEIGHT + V_FRONT_PORCH + V_SYNC_PULSE)); 
  end
  
  // Determine if in visible area
  assign inDisplayArea = (CounterX < WIDTH && CounterY < HEIGHT) ? 1'b1 : 1'b0;
  
  // Output sync signals
  assign vga_h_sync = vga_HS;
  assign vga_v_sync = vga_VS;
  
endmodule