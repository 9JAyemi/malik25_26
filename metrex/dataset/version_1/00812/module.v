module addsub_4bit (A, B, M, Y, O);

  input [3:0] A, B;
  input M;
  output reg [3:0] Y;
  output reg O;
  
  reg [4:0] temp;
  
  always @* begin
    if (M == 0) begin
      temp = A + B;
    end
    else begin
      temp = A - B;
    end
    Y = temp[3:0];
    O = temp[4];
  end
  
endmodule