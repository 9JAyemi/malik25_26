module adder (
  // Outputs
  S,
  // Inputs
  A, B, clk
  );
  
  input [7:0] A, B;
  input clk;
  output [7:0] S;
  
  
  
  
  
  reg [7:0] S_reg;
  

  always @(posedge clk) begin
    S_reg <= A + B;
  end
  
  assign S = S_reg;
  
endmodule