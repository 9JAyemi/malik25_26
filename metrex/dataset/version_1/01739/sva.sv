// Bindable SVA for module 'addition'
bind addition addition_sva u_addition_sva(.dut());

module addition_sva (addition dut);

  // Outputs must be known when inputs are known
  assert property (@(dut.a or dut.b)
    !$isunknown({dut.a, dut.b}) |-> ##0 !$isunknown({dut.sum, dut.overflow, dut.temp_sum, dut.carry}));

  // Core arithmetic consistency via temp_sum, sum, and carry
  assert property (@(dut.a or dut.b)
    !$isunknown({dut.a, dut.b}) |-> ##0
      (dut.temp_sum == ({1'b0, dut.a} + {1'b0, dut.b})) &&
      (dut.sum      == dut.temp_sum[7:0]) &&
      (dut.carry    == dut.temp_sum[8]));

  // Signed overflow correctness (two's-complement overflow)
  assert property (@(dut.a or dut.b)
    !$isunknown({dut.a, dut.b}) |-> ##0
      dut.overflow == ((dut.a[7] ~^ dut.b[7]) & (dut.sum[7] ^ dut.a[7])));

  // For opposite-sign adds, sum[7] must differ from carry (redundant RTL term never true)
  assert property (@(dut.a or dut.b)
    !$isunknown({dut.a, dut.b}) && (dut.a[7] ^ dut.b[7]) |-> ##0 (dut.sum[7] != dut.carry));

  // Coverage
  cover property (@(dut.a or dut.b) ##0 (dut.a[7]==1'b0 && dut.b[7]==1'b0 && dut.overflow)); // +/+: pos overflow
  cover property (@(dut.a or dut.b) ##0 (dut.a[7]==1'b1 && dut.b[7]==1'b1 && dut.overflow)); // -/-: neg overflow
  cover property (@(dut.a or dut.b) ##0 (dut.carry && !dut.overflow));                       // unsigned carry only
  cover property (@(dut.a or dut.b) ##0 (dut.a==8'h00 && dut.b==8'h00 && dut.sum==8'h00 && !dut.overflow)); // zero+zero

endmodule