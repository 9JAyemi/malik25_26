
module max_value (
  input [3:0] A,
  input [3:0] B,
  output reg [3:0] max
);

always @(*)
begin
  if(A > B)
    max = A;
  else
    max = B;
end

endmodule