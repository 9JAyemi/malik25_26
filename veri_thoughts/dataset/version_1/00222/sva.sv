// SVA for myNAND3. Bindable checker with internal-net checks and compact coverage.

module myNAND3_sva (
  input logic IN1, IN2, IN3,
  input logic QN,
  input logic nand1, nand2
);
  // Functional equivalence (4-state exact)
  a_func_port:    assert property (QN    === ~(IN1 & IN2 & IN3));
  a_nand1_func:   assert property (nand1 === ~(IN1 & IN2 & IN3));
  a_nand2_inv:    assert property (nand2 === ~nand1);
  a_qn_eq_nand1:  assert property (QN === nand1);

  // Knownness when inputs are known
  a_known_when_inputs_known: assert property (!$isunknown({IN1,IN2,IN3}) |-> (QN === ~(IN1 & IN2 & IN3)));

  // Deterministic corners (handle X/Z safely)
  a_any_zero_forces_one: assert property ((IN1===1'b0 || IN2===1'b0 || IN3===1'b0) |-> (QN===1'b1));
  a_all_one_forces_zero: assert property ((IN1===1'b1 && IN2===1'b1 && IN3===1'b1) |-> (QN===1'b0));

  // Truth-table coverage
  c_000: cover property (IN1===0 && IN2===0 && IN3===0 && QN===1);
  c_001: cover property (IN1===0 && IN2===0 && IN3===1 && QN===1);
  c_010: cover property (IN1===0 && IN2===1 && IN3===0 && QN===1);
  c_011: cover property (IN1===0 && IN2===1 && IN3===1 && QN===1);
  c_100: cover property (IN1===1 && IN2===0 && IN3===0 && QN===1);
  c_101: cover property (IN1===1 && IN2===0 && IN3===1 && QN===1);
  c_110: cover property (IN1===1 && IN2===1 && IN3===0 && QN===1);
  c_111: cover property (IN1===1 && IN2===1 && IN3===1 && QN===0);

  // Toggle-effect coverage (output changes when other inputs are high)
  c_tgl_in1_affects_q: cover property ($changed(IN1) && IN2===1 && IN3===1 && $changed(QN));
  c_tgl_in2_affects_q: cover property ($changed(IN2) && IN1===1 && IN3===1 && $changed(QN));
  c_tgl_in3_affects_q: cover property ($changed(IN3) && IN1===1 && IN2===1 && $changed(QN));
endmodule

bind myNAND3 myNAND3_sva u_myNAND3_sva (
  .IN1(IN1), .IN2(IN2), .IN3(IN3), .QN(QN),
  .nand1(nand1), .nand2(nand2)
);