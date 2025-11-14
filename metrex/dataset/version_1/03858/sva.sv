// SVA for dual_port_ram
module dual_port_ram_sva;
  default clocking cb @(posedge clk); endclocking

  // Basic X-safety on controls/addresses/data_in when enabled
  a_no_x_ctrl:  assert property (!$isunknown({we1,we2,addr1,addr2}));
  a_no_x_din1:  assert property (!we1 || !$isunknown(data_in1));
  a_no_x_din2:  assert property (!we2 || !$isunknown(data_in2));

  // Synchronous READ_FIRST behavior: outputs reflect previous-cycle mem at sampled address
  a_read1: assert property (1'b1 |-> ##1 (data_out1 == $past(mem[$past(addr1)])));
  a_read2: assert property (1'b1 |-> ##1 (data_out2 == $past(mem[$past(addr2)])));

  // If both ports read same address in a cycle, outputs match (same old data)
  a_same_addr_read_eq: assert property (addr1 == addr2 |-> data_out1 == data_out2);

  // WRITE semantics: updates are visible next cycle; Port2 wins same-address collision
  a_w2_update: assert property (we2 |-> ##1 (mem[$past(addr2)] == $past(data_in2)));
  a_w1_update_no_override: assert property ((we1 && !(we2 && (addr2 == addr1))) |-> ##1 (mem[$past(addr1)] == $past(data_in1)));
  a_collision_pref2: assert property ((we1 && we2 && (addr1 == addr2)) |-> ##1 (mem[$past(addr1)] == $past(data_in2)));

  // Read-after-write latency checks (new data observable on next-cycle reads)
  a_raw_w2_to_r1: assert property (we2 ##1 (addr1 == $past(addr2)) |-> (data_out1 == $past(data_in2)));
  a_raw_w2_to_r2: assert property (we2 ##1 (addr2 == $past(addr2)) |-> (data_out2 == $past(data_in2)));
  a_raw_w1_to_r1: assert property ((we1 && !(we2 && addr2 == addr1)) ##1 (addr1 == $past(addr1)) |-> (data_out1 == $past(data_in1)));
  a_raw_w1_to_r2: assert property ((we1 && !(we2 && addr2 == addr1)) ##1 (addr2 == $past(addr1)) |-> (data_out2 == $past(data_in1)));

  // Functional coverage
  c_w1:           cover property (we1 && !we2);
  c_w2:           cover property (!we1 && we2);
  c_both_diff:    cover property (we1 && we2 && (addr1 != addr2));
  c_both_same:    cover property (we1 && we2 && (addr1 == addr2));
  c_raw1_self:    cover property (we1 ##1 (addr1 == $past(addr1)));
  c_raw2_self:    cover property (we2 ##1 (addr2 == $past(addr2)));
  c_raw_cross_21: cover property (we2 ##1 (addr1 == $past(addr2)));
  c_raw_cross_12: cover property (we1 ##1 (addr2 == $past(addr1)));
  c_same_addr_read: cover property (addr1 == addr2);
endmodule

bind dual_port_ram dual_port_ram_sva sva_inst();