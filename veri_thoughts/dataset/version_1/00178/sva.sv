// SVA for my_module: concise, high-quality checks + coverage
module my_module_sva (input logic A, B, C, D, out, temp);
  default clocking @(posedge $global_clock); endclocking

  // Functional correctness (4-state accurate)
  a_temp_func: assert property (temp === ((B == 1'b1) ? A : C));
  a_out_func:  assert property (out  === ((D == 1'b1) ? ~temp : temp));

  // X-propagation semantics
  a_xprop_B_diff: assert property ($isunknown(B) && (A !== C) |-> $isunknown(temp));
  a_xprop_B_same: assert property ($isunknown(B) && (A === C) |-> (temp === A));
  a_xprop_D:      assert property ($isunknown(D)                 |-> $isunknown(out));

  // Functional coverage (paths + unknown controls)
  c_A_path_noinv: cover property (B === 1'b1 && D === 1'b0);
  c_A_path_inv:   cover property (B === 1'b1 && D === 1'b1);
  c_C_path_noinv: cover property (B === 1'b0 && D === 1'b0);
  c_C_path_inv:   cover property (B === 1'b0 && D === 1'b1);
  c_unk_ctrl:     cover property ($isunknown(B) || $isunknown(D));
  c_unk_B_merge:  cover property ($isunknown(B) && (A !== C));
  c_unk_B_pass:   cover property ($isunknown(B) && (A === C));
endmodule

// Bind into DUT (accesses internal wire temp)
bind my_module my_module_sva sva_inst (.A(A), .B(B), .C(C), .D(D), .out(out), .temp(temp));