// SystemVerilog Assertions for the given design
// Concise, high-quality checks with essential coverage

// Inverter (n0/n1)
module n_inv_sva(input A, input Y);
  // Functional check
  assert property (Y === ~A);
  // Coverage
  cover property (A==1'b0 && Y==1'b1);
  cover property (A==1'b1 && Y==1'b0);
endmodule
bind n0 n_inv_sva n0_chk(.A(A), .Y(Y));
bind n1 n_inv_sva n1_chk(.A(A), .Y(Y));

// Buffer (box)
module box_sva(input A, input Y);
  assert property (Y === A);
  cover property (A==1'b0 && Y==1'b0);
  cover property (A==1'b1 && Y==1'b1);
endmodule
bind box box_sva box_chk(.A(A), .Y(Y));

// Combiner (c)
module c_sva(input I, input [1:0] O);
  assert property (O === {~I, I});
  assert property (O[1] === ~O[0]);
  cover property (I==1'b0 && O==2'b01);
  cover property (I==1'b1 && O==2'b10);
endmodule
bind c c_sva c_chk(.I(I), .O(O));

// Top-level end-to-end and connectivity
module top_sva(input di, input [1:0] d, input [3:0] dout);
  // Internal relationships
  assert property (d[0] === ~di);
  assert property (d[1] === ~di);
  // Connectivity through boxes
  assert property (dout[0] === d[0]);
  assert property (dout[1] === d[1]);
  // c-inst outputs
  assert property (dout[2] === d[1]);     // O[0] = I = d[1]
  assert property (dout[3] === ~d[1]);    // O[1] = ~I = ~d[1]
  // End-to-end summary
  assert property ({dout[3],dout[2],dout[1],dout[0]} === {di, ~di, ~di, ~di});
  // Simple relational consistency
  assert property (dout[0] === dout[1] && dout[1] === dout[2]);
  assert property (dout[3] === ~dout[0]);
  // Coverage of both operating points
  cover property (di==1'b0 && dout==4'b0111);
  cover property (di==1'b1 && dout==4'b1000);
endmodule
// Note: 'do' is a SystemVerilog keyword; use escaped identifier when binding.
bind top top_sva top_chk(.di(di), .d(d), .dout(\do ));