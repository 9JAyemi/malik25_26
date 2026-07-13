
module full_adder(a, b, c_in, sum, c_out, p, g);
   input a, b, c_in;
   output sum, c_out, p, g;

   assign {c_out, sum} = a + b + c_in;
   assign p = a & b;
   assign g = a ^ b; // Corrected the expression for g
endmodule