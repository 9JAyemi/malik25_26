// SVA for karnaugh_map
// Bind a free-running clk from your environment.

module karnaugh_map_sva #(parameter bit FULL_MINTERM_COV = 1) (
  input logic clk,
  input logic A, B, C, D,
  input logic F
);
  default clocking cb @(posedge clk); endclocking

  // Sanity
  a_known:           assert property (!$isunknown({A,B,C,D,F}));

  // Functional equivalence (simplified boolean)
  a_func:            assert property (F == (C ^ D) ^ (B & ~A));

  // Stability: if inputs held, output held
  a_stable:          assert property ($stable({A,B,C,D}) |-> $stable(F));

  // Output changes are caused by input changes (at sample boundaries)
  a_change_caused:   assert property ($changed(F) |-> $changed({A,B,C,D}));

  // Functional coverage of key classes
  c_xnor_branch_1:   cover property ((B & ~A) && !(C ^ D) &&  F);
  c_xnor_branch_0:   cover property ((B & ~A) &&  (C ^ D) && !F);
  c_xor_branch_1:    cover property (!(B & ~A) && (C ^ D) &&  F);
  c_xor_branch_0:    cover property (!(B & ~A) && !(C ^ D) && !F);

  // Toggle coverage on F
  c_rose:            cover property ($rose(F));
  c_fell:            cover property ($fell(F));

  // Full minterm input coverage (all 16 input combinations)
  if (FULL_MINTERM_COV) begin
    genvar i;
    for (i = 0; i < 16; i++) begin : g_cov
      c_minterm: cover property ({A,B,C,D} == i[3:0]);
    end
  end
endmodule

// Example bind (adjust clk name as appropriate):
// bind karnaugh_map karnaugh_map_sva sva(.clk(clk), .A(A), .B(B), .C(C), .D(D), .F(F));