module half_full_adder (
  input A,
  input B,
  input C_in,
  output S,
  output C_out
);

  wire H_S, H_C, F_C;
  
  // Instantiate half-adder
  half_adder HA1(A, B, H_S, H_C);
  
  // Instantiate full-adder
  full_adder FA1(A, B, C_in, S, F_C);
  
  // Connect carry output of half-adder to carry input of full-adder
  assign C_out = H_C | F_C;

endmodule

// Half-adder module
module half_adder (
  input A,
  input B,
  output S,
  output C
);

  assign S = A ^ B;
  assign C = A & B;

endmodule

// Full-adder module
module full_adder (
  input A,
  input B,
  input C_in,
  output S,
  output C_out
);

  wire H1_S, H1_C, H2_S, H2_C;
  
  // Instantiate two half-adders
  half_adder HA1(A, B, H1_S, H1_C);
  half_adder HA2(H1_S, C_in, H2_S, H2_C);
  
  // Calculate sum and carry
  assign S = H2_S;
  assign C_out = H1_C | H2_C;

endmodule