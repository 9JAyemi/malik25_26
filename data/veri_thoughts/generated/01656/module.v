module adder (input [7:0] in1, input [7:0] in2, output [8:0] res);
  wire [8:0] temp;
  
  assign temp = in1 + in2;
  assign res = {temp[8], temp};
endmodule