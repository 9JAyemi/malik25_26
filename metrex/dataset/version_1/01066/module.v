module WDT (
  input clk, rst,
  output wdt
);

  parameter t = 10; // timeout period in clock cycles
  
  reg [31:0] counter;
  
  always @(posedge clk) begin
    if (rst) begin
      counter <= 0;
    end
    else begin
      counter <= counter + 1;
    end
  end
  
  assign wdt = (counter >= t) ? 1'b1 : 1'b0;
  
endmodule