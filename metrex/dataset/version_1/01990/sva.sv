// SVA bind file for complement
module complement_sva (input [3:0] A, input [3:0] C);

  // Functional correctness (evaluate after delta to avoid race with comb update)
  property p_func; @(A or C) 1 |-> ##0 (C == (~A + 4'b0001)); endproperty
  assert property (p_func);

  // Additive inverse with carry-out: {0,A}+{0,C} == 16
  property p_add_inverse; @(A or C) 1 |-> ##0 (({1'b0,A} + {1'b0,C}) == 5'b1_0000); endproperty
  assert property (p_add_inverse);

  // Involution: two's complement twice returns original
  property p_involution; @(A or C) 1 |-> ##0 ((~C + 4'b0001) == A); endproperty
  assert property (p_involution);

  // No X/Z propagation: known A implies known C
  property p_no_x; @(A or C) (!$isunknown(A)) |-> ##0 (!$isunknown(C)); endproperty
  assert property (p_no_x);

  // Edge cases
  assert property (@(A) (A==4'h0) |-> ##0 (C==4'h0));
  assert property (@(A) (A==4'h8) |-> ##0 (C==4'h8));

  // Functional coverage
  covergroup cg_A @(A);
    coverpoint A { bins all_vals[] = {[0:15]}; }
  endgroup
  cg_A cg_A_i = new();

  cover property (@(A) ##0 (({1'b0,A} + {1'b0,C}) == 5'b1_0000));
  cover property (@(A) (A==4'h0) ##0 (C==4'h0));
  cover property (@(A) (A==4'h8) ##0 (C==4'h8));

endmodule

bind complement complement_sva sva_inst(.A(A), .C(C));