// SVA for top_module and its submodules (concise, full functional checks + key coverage)

module top_module_sva (input [7:0] A, B, input enable, input EQ, GT, OR);
  // No X/Z on outputs when inputs are clean
  assert property (@(A or B or enable) !$isunknown({A,B,enable}) |-> !$isunknown({EQ,GT,OR}));

  // Output consistency
  assert property (@(A or B or enable) OR == (EQ || GT));
  assert property (@(A or B or enable) !(EQ && GT));

  // Functional equivalence to intended behavior
  assert property (@(A or B or enable) !enable |-> (EQ == (A==B) && GT == (A>B) && OR == (A>=B)));
  assert property (@(A or B or enable)  enable |-> (EQ && !GT && OR));

  // Minimal functional coverage
  cover property (@(A or B or enable) !enable && (A==B) && EQ && !GT && OR);
  cover property (@(A or B or enable) !enable && (A>B)  && GT && !EQ && OR);
  cover property (@(A or B or enable) !enable && (A<B)  && !GT && !EQ && !OR);
  cover property (@(A or B or enable)  enable && EQ && !GT && OR);
  cover property (@(A or B or enable) $rose(OR));
  cover property (@(A or B or enable) $fell(OR));
endmodule

module mux_2to1_sva (input [7:0] in0, in1, input sel, input [7:0] out);
  assert property (@(in0 or in1 or sel) (sel==1'b0) |-> (out==in0));
  assert property (@(in0 or in1 or sel) (sel==1'b1) |-> (out==in1));
  assert property (@(in0 or in1 or sel) !$isunknown({in0,in1,sel}) |-> !$isunknown(out));

  cover property (@(in0 or in1 or sel) sel==1'b0);
  cover property (@(in0 or in1 or sel) sel==1'b1);
endmodule

module comp_8bit_sva (input [7:0] A, B, input EQ, GT);
  assert property (@(A or B) EQ == (A==B));
  assert property (@(A or B) GT == (A>B));
  assert property (@(A or B) !(EQ && GT));
  assert property (@(A or B) !$isunknown({A,B}) |-> !$isunknown({EQ,GT}));

  cover property (@(A or B) (A==B) && EQ && !GT);
  cover property (@(A or B) (A>B)  && GT && !EQ);
  cover property (@(A or B) (A<B)  && !GT && !EQ);
endmodule

// Bind assertions to DUT
bind top_module top_module_sva top_module_sva_i (.*);
bind mux_2to1   mux_2to1_sva   mux_2to1_sva_i   (.*);
bind comp_8bit  comp_8bit_sva  comp_8bit_sva_i  (.*);