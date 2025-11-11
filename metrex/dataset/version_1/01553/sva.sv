// SVA checker to bind into AdderSubtractor
module AdderSubtractor_sva(input logic clk, input logic rst_n);
  // Bound into AdderSubtractor scope; can see A,B,Sub,S,Cout,A_comp,B_comp,temp_sum
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Sanity: no X/Z on inputs/outputs
  a_no_x_in:  assert property (!$isunknown({A,B,Sub}));
  a_no_x_out: assert property (!$isunknown({S,Cout}));

  // Internal signal correctness
  a_bcomp_def:  assert property (B_comp == (~B + 4'd1));
  a_acomp_def:  assert property (A_comp == (~A + 4'd1));
  a_temp_sum:   assert property (temp_sum == (Sub ? ({1'b0,A}+{1'b0,B_comp})
                                                  : ({1'b0,A}+{1'b0,B})));
  a_s_lowbits:  assert property (S == temp_sum[3:0]);

  // Functional equivalence
  a_add_eq: assert property (!Sub |-> {Cout,S} == ({1'b0,A} + {1'b0,B}));
  a_sub_eq: assert property ( Sub |-> (S == (({1'b0,A} + {1'b0,~B} + 5'd1)[3:0]))
                                      && (Cout == (A >= B))
                                      && (Cout == ({1'b0,A} + {1'b0,~B} + 5'd1)[4]));

  // Coverage
  c_mode_add:    cover property (!Sub);
  c_mode_sub:    cover property ( Sub);
  c_add_carry0:  cover property (!Sub && (({1'b0,A}+{1'b0,B})[4] == 1'b0));
  c_add_carry1:  cover property (!Sub && (({1'b0,A}+{1'b0,B})[4] == 1'b1));
  c_sub_equal:   cover property ( Sub && (A == B) && (S == 4'h0) && (Cout == 1'b1));
  c_sub_borrow:  cover property ( Sub && (A <  B) && (Cout == 1'b0));
  c_sub_noborr:  cover property ( Sub && (A >  B) && (Cout == 1'b1));
endmodule

// Bind into DUT (provide clk/rst_n from your TB)
bind AdderSubtractor AdderSubtractor_sva sva_i(.clk(clk), .rst_n(rst_n));