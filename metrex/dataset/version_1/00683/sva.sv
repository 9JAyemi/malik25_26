// SVA for shift_register_4bit
// Bind example (tool-dependent):
//   bind shift_register_4bit shift_register_4bit_sva u_sva(.*);

module shift_register_4bit_sva (shift_register_4bit dut);

  default clocking cb @(posedge dut.CLK); endclocking

  // Combinational mappings
  a_map_so: assert property (dut.SO == dut.shift_reg[0]);
  a_map_q3: assert property (dut.Q3 == dut.shift_reg[3]);
  a_map_s1: assert property (dut.stage1_out == dut.next_reg[2:0]);
  a_map_s2: assert property (dut.stage2_out[0] == dut.next_reg[3]);

  // Pipeline/register update relationships
  a_sr_from_nr: assert property ( !$isunknown($past(dut.next_reg)) |-> (dut.shift_reg == $past(dut.next_reg)) );

  a_nr_update:  assert property (
    !$isunknown($past(dut.shift_reg)) |-> 
      (dut.next_reg == { $past(dut.shift_reg[2]),
                         $past(dut.shift_reg[1]),
                         $past(dut.shift_reg[0]),
                         dut.SI })
  );

  // End-to-end observable latencies
  a_so_latency: assert property ( !$isunknown($past(dut.SI))    |-> (dut.SO == $past(dut.SI,1)) );
  a_q3_latency: assert property ( !$isunknown($past(dut.SI,7))  |-> (dut.Q3 == $past(dut.SI,7)) );

  // Two-cycle vector relationship (from shift_reg and SI)
  a_two_cycle: assert property (
    !$isunknown($past({dut.shift_reg,dut.SI},2)) |->
      (dut.shift_reg == { $past(dut.shift_reg[2],2),
                          $past(dut.shift_reg[1],2),
                          $past(dut.shift_reg[0],2),
                          $past(dut.SI,1) })
  );

  // No X/Z on key observables after first valid cycle
  a_no_x: assert property ( !$isunknown($past(dut.next_reg)) |-> !$isunknown({dut.shift_reg,dut.SO,dut.Q3}) );

  // Coverage
  c_so:  cover property ( dut.SI ##1 dut.SO );
  c_q3:  cover property ( dut.SI ##7 dut.Q3 );
  c_walk1: cover property ( $rose(dut.SI) ##1 $rose(dut.SO) ##2 $rose(dut.shift_reg[1]) ##2 $rose(dut.shift_reg[2]) ##2 $rose(dut.Q3) );

endmodule