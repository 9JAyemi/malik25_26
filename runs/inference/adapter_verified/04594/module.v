module comparator_4bit (
  input [3:0] A,
  input [3:0] B,
  output reg [1:0] result
);

  always @(*)
  begin
    if (A > B) 
      result = 2'b01;
    else if (A < B) 
      result = 2'b10;
    else 
      result = 2'b00;
  end

endmodule
