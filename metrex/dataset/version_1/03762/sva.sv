// SVA for multiplier — concise, high-quality checks and coverage
module multiplier_sva (multiplier dut);

  default clocking @(posedge dut.clk); endclocking

  // Helpers to match DUT arithmetic (13-bit ops, zero-extended to 26)
  function automatic logic [25:0] zext_shift13(input logic [12:0] v, input logic [10:0] sh);
    zext_shift13 = {13'd0, (v << sh)};
  endfunction
  function automatic logic [12:0] neg13(input logic [12:0] v);
    neg13 = (~v + 13'd1);
  endfunction

  // Outputs mirror regs and zero-extend to 27 bits
  assert property (dut.Y == {1'b0, dut.Y_reg} && dut.Z == {1'b0, dut.Z_reg});

  // A_reg/B_reg sample ports each cycle
  assert property (##0 (dut.A_reg == dut.A && dut.B_reg == dut.B));

  // Counter increments every cycle and rolls over
  assert property (!$isunknown($past(dut.i)) |-> ##0 dut.i == $past(dut.i) + 11'd1);
  assert property ($past(dut.i) == 11'h7FF |-> ##0 dut.i == 11'd0);

  // Clear on prior i==0
  assert property ($past(dut.i) == 11'd0 |-> ##0 (dut.Y == 27'd0 && dut.Z == 27'd0));

  // Hold when no add (prior i!=0 and prior B_reg[0]==0)
  assert property (($past(dut.i) != 11'd0) && ($past(dut.B_reg[0]) == 1'b0)
                   |-> ##0 (dut.Y == $past(dut.Y) && dut.Z == $past(dut.Z)));

  // Accumulate when add (prior i!=0 and prior B_reg[0]==1)
  assert property (($past(dut.i) != 11'd0) && ($past(dut.B_reg[0]) == 1'b1) |-> ##0
                   (dut.Y == $past(dut.Y) + {1'b0, zext_shift13($past(dut.A_reg), $past(dut.i)-1)} &&
                    dut.Z == $past(dut.Z) + {1'b0, zext_shift13(neg13($past(dut.A_reg)), $past(dut.i)-1)}));

  // Cross-check recurrence of Y+Z (captures carry from 13-bit add)
  assert property (($past(dut.i) != 11'd0) && ($past(dut.B_reg[0]) == 1'b1) |-> ##0
                   (dut.Y + dut.Z) == ($past(dut.Y) + $past(dut.Z)) + (27'd1 << (13 + ($past(dut.i)-1))));
  assert property (($past(dut.i) != 11'd0) && ($past(dut.B_reg[0]) == 1'b0) |-> ##0
                   (dut.Y + dut.Z) == ($past(dut.Y) + $past(dut.Z)));

  // Coverage
  cover property (dut.i == 11'd0);                                      // clear event
  cover property (($past(dut.i) != 11'd0) && $past(dut.B_reg[0]) == 1); // accumulate event
  cover property ($past(dut.i) == 11'h7FF ##0 dut.i == 11'd0);          // rollover

endmodule

bind multiplier multiplier_sva sva_inst;