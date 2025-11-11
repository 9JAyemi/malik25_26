
module csa_generate_adder_32bit #(
  parameter SIZE = 32
  )
  (
  input  [SIZE-1:0] A,
  input  [SIZE-1:0] B,
  output [SIZE-1:0] S,
  output C_OUT
  );

  wire [SIZE:0] C;

  assign C[SIZE] = 0;
  assign {C[SIZE-1:0], S} = A + B + C[SIZE];
  assign C_OUT = C[SIZE];

endmodule