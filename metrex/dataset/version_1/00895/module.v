
module one_shot (
  input trig,
  input clk,
  input rst,
  output out
);

  parameter t = 10; // duration of output pulse in clock cycles
  
  reg [31:0] count = 0;
  reg pulse = 0;
  reg out_reg = 0; // Registered output
  
  always @(posedge clk) begin
    if (rst) begin
      count <= 0;
      pulse <= 0;
      out_reg <= 0;
    end
    else if (trig && !pulse) begin
      count <= 0;
      pulse <= 1;
      out_reg <= 1;
    end
    else if (pulse && count < t-1) begin
      count <= count + 1;
      out_reg <= 1;
    end
    else if (pulse && count == t-1) begin
      count <= 0;
      pulse <= 0;
      out_reg <= 0;
    end
    else begin
      out_reg <= 0;
    end
  end
  
  assign out = out_reg; // Drive output from registered value
  
endmodule
