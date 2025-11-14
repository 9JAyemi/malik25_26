
module adder_2bit(input [1:0] A, B, S, output [1:0] O);

  wire [1:0] sum;
  wire [1:0] diff;

  wire s_not;
  not (s_not, S);

  // Calculate sum and difference
  assign sum = A + B;
  assign diff = {A[1] ^ B[1], A[0] ^ B[0]} + {~B[1], ~B[0], 1'b0};

  // Use mux2to1 to select output based on S
  assign O = s_not ? sum : diff;

endmodule
