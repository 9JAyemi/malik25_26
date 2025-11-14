module MUX4 (
    A,
    B,
    C,
    D,
    S0,
    S1,
    Y
);
  input A, B, C, D, S0, S1;
  output Y;
  
  wire MUX0_out, MUX1_out;
  
  // Instantiating 2-to-1 multiplexers
  MUX2x1 MUX0 (
      .A (A),
      .B (B),
      .S (S0),
      .Q (MUX0_out)
  );
  
  MUX2x1 MUX1 (
      .A (C),
      .B (D),
      .S (S0),
      .Q (MUX1_out)
  );
  
  // Final 2-to-1 multiplexer
  MUX2x1 MUX2 (
      .A (MUX0_out),
      .B (MUX1_out),
      .S (S1),
      .Q (Y)
  );
  
endmodule

// 2-to-1 multiplexer building block
module MUX2x1 (
    A,
    B,
    S,
    Q
);
  input A, B, S;
  output Q;
  
  assign Q = (S == 1'b0) ? A : B;
  
endmodule