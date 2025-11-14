// SVA for xor_shift_register
// Bind this file; focuses on correctness, minimal but high-value checks and coverage.

module xor_shift_register_sva (xor_shift_register dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff ($isunknown({dut.a,dut.b,dut.shift_reg,dut.q}));

  // NOR chain correctness
  a_n1_is_nor:       assert property (dut.n1 == ~(dut.a | dut.b));
  a_chain_inv_2:     assert property (dut.n2 == ~dut.n1);
  a_chain_inv_3:     assert property (dut.n3 == ~dut.n2);
  a_chain_inv_4:     assert property (dut.n4 == ~dut.n3);
  a_chain_inv_5:     assert property (dut.n5 == ~dut.n4);
  a_chain_inv_6:     assert property (dut.n6 == ~dut.n5);
  a_chain_inv_7:     assert property (dut.n7 == ~dut.n6);
  a_chain_inv_8:     assert property (dut.n8 == ~dut.n7);
  a_and_out_is_nor:  assert property (dut.and_out == ~dut.n8);
  a_and_out_func:    assert property (dut.and_out == ~(dut.a | dut.b));

  // Shift register behavior (shift left, insert 0)
  a_shift:           assert property (!$isunknown($past(dut.shift_reg,1)))
                                   |-> (dut.shift_reg == { $past(dut.shift_reg,1)[6:0], 1'b0 });

  // q formation (bitwise XOR with only LSB masked by and_out per RTL sizing)
  a_q_map:           assert property (dut.q == (dut.shift_reg ^ {7'b0, dut.and_out}));

  // Liveness/invariants of shift_reg
  a_flush_8:         assert property (dut.shift_reg != 8'h00 |-> ##[1:8] dut.shift_reg == 8'h00);
  a_zero_sticky:     assert property (dut.shift_reg == 8'h00 |=> dut.shift_reg == 8'h00);

  // Functional coverage
  c_and_out_00:      cover property (dut.a==0 && dut.b==0 && dut.and_out==1);
  c_and_out_01:      cover property (dut.a==0 && dut.b==1 && dut.and_out==0);
  c_and_out_10:      cover property (dut.a==1 && dut.b==0 && dut.and_out==0);
  c_and_out_11:      cover property (dut.a==1 && dut.b==1 && dut.and_out==0);
  c_flush:           cover property (dut.shift_reg != 8'h00 ##[1:8] dut.shift_reg == 8'h00);

endmodule

bind xor_shift_register xor_shift_register_sva u_xor_shift_register_sva(.dut());