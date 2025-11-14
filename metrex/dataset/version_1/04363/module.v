module selector ( input [3:0] pm0, input [3:0] pm1, input [3:0] pm2, input [3:0] pm3, output d0, output d1 );
  wire n1, n2, n3, n4, n5, n6, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22;

  // First, implement the logic for d0
  // The AND gate takes as input the output of two NOR gates
  // Each NOR gate takes as input two of the four input bits
  assign n1 = ~(pm0[0] | pm0[1]);
  assign n2 = ~(pm0[2] | pm0[3]);
  assign n3 = ~(pm1[0] | pm1[1]);
  assign n4 = ~(pm1[2] | pm1[3]);
  assign n5 = n1 & n2;
  assign n6 = n3 & n4;
  // The output of the AND gate is used as input to the 2-to-1 multiplexer
  assign d0 = n5 | n6;

  // Next, implement the logic for d1
  // The AND gate takes as input the output of two NAND gates
  // Each NAND gate takes as input two of the four input bits
  assign n8 = ~(pm2[0] & pm2[1]);
  assign n9 = ~(pm2[2] & pm2[3]);
  assign n10 = ~(pm3[0] & pm3[1]);
  assign n11 = ~(pm3[2] & pm3[3]);
  assign n12 = n8 & n9;
  assign n13 = n10 & n11;
  // The output of the AND gate is used as input to the 2-to-1 multiplexer
  assign n14 = n12 | n13;
  // The output of the 2-to-1 multiplexer is used as input to the OR gate
  // The AOI gate takes as input three of the four input bits
  assign n15 = ~(pm0[0] & pm1[0] & pm2[0]);
  assign n16 = ~(pm0[1] & pm1[1] & pm2[1]);
  assign n17 = ~(pm0[2] & pm1[2] & pm2[2]);
  assign n18 = ~(pm0[3] & pm1[3] & pm2[3]);
  assign n19 = n15 | n16;
  assign n20 = n17 | n18;
  assign n21 = n19 | n20;
  // The output of the AOI gate is inverted to produce d1
  assign n22 = ~n14;
  assign d1 = n21 | n22;
endmodule