// SVA for parity_checker
module parity_checker_sva;
  // Bind into DUT scope; all names below refer to parity_checker internals
  default clocking cb @(posedge clk); endclocking

  // Start checking after two clocks to avoid power-up Xs
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end
  default disable iff (!past2);

  // Stage-1 pipeline behavior
  ap_s1_0_capt:  assert property (stage1_data[0] == $past(data[1:0]));
  ap_s1_1_shift: assert property (stage1_data[1] == $past(stage1_data[0]));

  // Stage-2 combinational correctness
  ap_s2_0_zero:  assert property (stage2_data[0] == 2'b00);
  ap_s2_1_xor:   assert property (stage2_data[1] == (stage1_data[1] ^ stage1_data[0]));

  // Output register correctness
  ap_parity_from_s2: assert property (parity == $past(^stage2_data[1]));
  // End-to-end check from input LSBs over two cycles
  ap_parity_e2e: assert property (
    !$isunknown({$past(data[1:0]), $past(data[1:0],2)}) |->
      parity == ^($past(data[1:0]) ^ $past(data[1:0],2))
  );

  // No X/Z on key state/output after init
  ap_no_x: assert property (!$isunknown({stage1_data[0], stage1_data[1], stage2_data[1], parity}));

  // Functional coverage
  cp_s2_00: cover property (stage2_data[1] == 2'b00);
  cp_s2_01: cover property (stage2_data[1] == 2'b01);
  cp_s2_10: cover property (stage2_data[1] == 2'b10);
  cp_s2_11: cover property (stage2_data[1] == 2'b11);
  cp_p0:    cover property (parity == 1'b0);
  cp_p1:    cover property (parity == 1'b1);
  cp_p01:   cover property (parity==0 ##1 parity==1);
  cp_p10:   cover property (parity==1 ##1 parity==0);
  cp_shift_change: cover property (stage1_data[1] != stage1_data[0]);
  cp_shift_hold:   cover property (stage1_data[1] == stage1_data[0]);
endmodule

bind parity_checker parity_checker_sva sva();