module add_sub_4bit(
  input [3:0] A,
  input [3:0] B,
  input SUB,
  output reg [3:0] SUM
);

  always @(*) begin
    if(SUB == 0) begin
      SUM = A + B;
    end
    else begin
      SUM = A - B;
    end
  end
  
endmodule