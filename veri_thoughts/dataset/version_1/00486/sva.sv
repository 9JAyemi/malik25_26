// SVA for my_module
module my_module_sva (my_module dut);

  // Create a combinational sampling event for clockless DUT
  event comb_ev; 
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Sanity: outputs known when inputs are known
  a_known: assert property (!$isunknown({dut.A1,dut.A2,dut.A3,dut.A4,dut.B1}) |-> !$isunknown({dut.X_A,dut.X_B,dut.X}));

  // Stage 1 function
  a_stage1: assert property (dut.X_A === (dut.A1 ? dut.A2 : (dut.A3 ^ dut.A4)));

  // Stage 2 function
  a_stage2: assert property (dut.X_B === (dut.X_A ^ dut.B1));

  // Output equals stage 2
  a_out_eq: assert property (dut.X === dut.X_B);

  // End-to-end function
  a_e2e: assert property (dut.X === ((dut.A1 ? dut.A2 : (dut.A3 ^ dut.A4)) ^ dut.B1));

  // Coverage: exercise all control paths and XOR outcomes
  c_path_00: cover property (!dut.A1 && !dut.B1);
  c_path_01: cover property (!dut.A1 &&  dut.B1);
  c_path_10: cover property ( dut.A1 && !dut.B1);
  c_path_11: cover property ( dut.A1 &&  dut.B1);
  c_xor_0:  cover property (!dut.A1 && ((dut.A3 ^ dut.A4) == 1'b0));
  c_xor_1:  cover property (!dut.A1 && ((dut.A3 ^ dut.A4) == 1'b1));

  // Coverage: B1 toggle inverts X when X_A is stable
  c_b1_tog_inv_x: cover property ($stable(dut.X_A) && !$isunknown({dut.X_A,dut.B1,dut.X}) &&
                                  (dut.B1 != $past(dut.B1)) && (dut.X != $past(dut.X)));

endmodule

bind my_module my_module_sva sva_u();