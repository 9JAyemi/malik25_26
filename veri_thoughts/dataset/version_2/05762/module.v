module Hyperbolic_Functions (
  input [2:0] x, 
  output reg [15:0] sineh,
  output reg [15:0] cosh,
  output reg [15:0] tanh
);

  always @(*) begin
    case(x)
      3'd0: begin
        sineh = 16'd0; 
        cosh = 16'd1; 
        tanh = 16'd0;
      end
      3'd1: begin
        sineh = 16'd1; 
        cosh = 16'd1; 
        tanh = 16'd1; 
      end
      3'd2: begin
        sineh = 16'd3; 
        cosh = 16'd4; 
        tanh = 16'd1;
      end
      3'd3: begin
        sineh = 16'd10; 
        cosh = 16'd11; 
        tanh = 16'd1; 
      end
      3'd4: begin
        sineh = 16'd27;
        cosh = 16'd28; 
        tanh = 16'd1; 
      end
      default: begin
        sineh = 16'd0;
        cosh = 16'd1;
        tanh = 16'd0;
      end
    endcase
  end

endmodule
