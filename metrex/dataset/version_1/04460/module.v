
module distance_calculator (
  input signed [31:0] x1,
  input signed [31:0] y1,
  input signed [31:0] z1,
  input signed [31:0] x2,
  input signed [31:0] y2,
  input signed [31:0] z2,
  output reg [31:0] distance
);

localparam I32 = 32;
localparam SCALE = 16;

function integer abs (input integer a);
  abs = a >= 0 ? a : -a ;
endfunction

function integer pow2 (input integer a);
  pow2 = a*a;
endfunction

always @(*) begin
  distance = 0;
  distance =  distance + pow2(abs(x2 - x1));
  distance = distance + pow2(abs(y2 - y1));
  distance = distance + pow2(abs(z2 - z1));
  distance = distance >> SCALE ;
end
  
endmodule