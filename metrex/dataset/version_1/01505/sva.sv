// Bindable SVA for excess_3
module excess_3_sva (excess_3 dut, input logic clk);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on interface and key internals
  a_no_x: assert property (!$isunknown({dut.binary, dut.stage1_out, dut.stage2_out, dut.bcd}));

  // Core functionality: Excess-3 mapping
  a_excess3: assert property (dut.bcd == (dut.binary + 4'd3));

  // Internal stage checks
  a_stage1_add3:          assert property (dut.stage1_out == (dut.binary + 4'd3));
  a_no_stage2_correction: assert property (dut.stage2_out == dut.stage1_out);
  a_no_final_correction:  assert property (dut.bcd == dut.stage2_out);

  // Step-to-step coherence when input increments by 1
  a_inc_tracks: assert property (
    !$isunknown({$past(dut.binary), $past(dut.bcd)}) &&
    ($past(dut.binary) + 4'd1 == dut.binary) |-> ($past(dut.bcd) + 4'd1 == dut.bcd)
  );

  // Coverage: key values and internal thresholding
  c_zero:   cover property (dut.binary == 4'd0  && dut.bcd == 4'd3);
  c_six:    cover property (dut.binary == 4'd6  && dut.bcd == 4'd9);
  c_seven:  cover property (dut.binary == 4'd7  && dut.bcd == 4'd10);
  c_nine:   cover property (dut.binary == 4'd9  && dut.bcd == 4'd12);
  c_wrap:   cover property (dut.binary == 4'd15 && dut.bcd == 4'd2);
  c_stage1_ge10: cover property (dut.stage1_out >= 5'd10);
  c_stage2_ge10: cover property (dut.stage2_out >= 5'd10);
endmodule

// Example bind (from testbench):
// bind excess_3 excess_3_sva i_excess_3_sva(.clk(tb_clk));