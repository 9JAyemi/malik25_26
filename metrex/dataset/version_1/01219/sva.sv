// SVA for nand2
module nand2_sva(input logic A, B, Y);

  // Sample on any input/output edge
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y); endclocking

  // Functional equivalence across 4-state logic
  a_func: assert property (Y === ~(A & B));

  // Truth-table coverage (2-state)
  c_tt00: cover property (A===1'b0 && B===1'b0 && Y===1'b1);
  c_tt01: cover property (A===1'b0 && B===1'b1 && Y===1'b1);
  c_tt10: cover property (A===1'b1 && B===1'b0 && Y===1'b1);
  c_tt11: cover property (A===1'b1 && B===1'b1 && Y===1'b0);

  // Output edge coverage
  c_y_rise: cover property ($rose(Y));
  c_y_fall: cover property ($fell(Y));

  // X-behavior coverage
  c_x_masked:     cover property (((A===1'b0 && $isunknown(B)) || (B===1'b0 && $isunknown(A))) && Y===1'b1);
  c_x_propagates: cover property (((A===1'b1 && $isunknown(B)) || (B===1'b1 && $isunknown(A))) && $isunknown(Y));

endmodule

bind nand2 nand2_sva u_nand2_sva(.A(A), .B(B), .Y(Y));