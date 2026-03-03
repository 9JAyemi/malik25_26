// SVA for the given design. Uses $global_clock to sample combinational logic post-settle.
// Bind these modules after compiling the DUT.

module sva_half_adder(half_adder m);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness
  a_ha_sum:  assert property (##0 (m.sum  === (m.a ^ m.b)));
  a_ha_cout: assert property (##0 (m.cout === (m.a & m.b)));

  // Key coverage: all input combos and carry generation
  c_ha_00: cover property (##0 (m.a==0 && m.b==0 && m.sum==0 && m.cout==0));
  c_ha_01: cover property (##0 (m.a==0 && m.b==1 && m.sum==1 && m.cout==0));
  c_ha_10: cover property (##0 (m.a==1 && m.b==0 && m.sum==1 && m.cout==0));
  c_ha_11: cover property (##0 (m.a==1 && m.b==1 && m.sum==0 && m.cout==1));
endmodule

module sva_bitwise_or(bitwise_OR m);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness
  a_bo_or:  assert property (##0 (m.out_or_bitwise === (m.a_bitwise | m.b_bitwise)));
  a_bo_lor: assert property (##0 (m.out_or_logical === (|{m.a_bitwise, m.b_bitwise})));
  a_bo_not: assert property (##0 (m.out_not === ~{m.a_bitwise, m.b_bitwise}));

  // Key coverage
  c_bo_zero_in:   cover property (##0 (m.a_bitwise==3'b000 && m.b_bitwise==3'b000 &&
                                     m.out_or_bitwise==3'b000 && m.out_or_logical==0));
  c_bo_all_ones:  cover property (##0 (m.a_bitwise==3'b111 && m.b_bitwise==3'b111 &&
                                     m.out_or_bitwise==3'b111 && m.out_or_logical==1));
  c_bo_mix_bits:  cover property (##0 (m.a_bitwise==3'b101 && m.b_bitwise==3'b010 &&
                                     m.out_or_bitwise==3'b111 && m.out_or_logical==1));
  c_bo_not_edges: cover property (##0 (m.out_not==~{3'b000,3'b000})) &&
                   cover property (##0 (m.out_not==~{3'b111,3'b111}));
  c_bo_lor_0_1:   cover property (##0 (m.out_or_logical==0)) &&
                   cover property (##0 (m.out_or_logical==1));
endmodule

module sva_functional_module(functional_module m);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness (3-bit truncated sum)
  a_fm_add: assert property (##0 (m.out_final === (m.out_or_bitwise + m.sum)));

  // Key coverage: sum contributes/no-op and wraparound
  c_fm_sum0:  cover property (##0 (m.sum==1'b0 && m.out_final==m.out_or_bitwise));
  c_fm_sum1:  cover property (##0 (m.sum==1'b1));
  c_fm_wrap:  cover property (##0 (m.sum==1'b1 && m.out_or_bitwise==3'b111 &&
                                  m.out_final==3'b000));
endmodule

module sva_top(top_module m);
  default clocking cb @(posedge $global_clock); endclocking

  // Passthrough from functional_module to top output
  a_top_pass: assert property (##0 (m.out_sum === m.out_final));

  // Simple integration coverage: exercise both 0 and nonzero outputs
  c_top_zero:   cover property (##0 (m.out_sum==3'b000));
  c_top_nonzero:cover property (##0 (m.out_sum!=3'b000));
endmodule

// Bind statements
bind half_adder        sva_half_adder      sva_ha   (.*);
bind bitwise_OR        sva_bitwise_or      sva_bo   (.*);
bind functional_module sva_functional_module sva_fm (.*);
bind top_module        sva_top             sva_tp   (.*);