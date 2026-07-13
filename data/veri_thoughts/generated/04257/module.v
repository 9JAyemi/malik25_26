module concat_split_vectors (
  input [7:0] a,
  input [7:0] b,
  output reg [3:0] w,
  output reg [3:0] x,
  output reg [3:0] y,
  output reg [3:0] z
);

  reg [15:0] concat;
  
  always @ (a or b) begin
    concat = {a, b};
  end
  
  assign {w, x, y, z} = concat + 4'b11;
  
endmodule
