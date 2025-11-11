// SVA for ripple_shift
module ripple_shift_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |=> shift_reg == 3'b000);
  assert property (reset && $past(reset) |-> shift_reg == 3'b000);

  // Parallel load (priority over shift)
  assert property (disable iff (reset)
                   (parallel_load != 3'b000) |=> shift_reg == $past(parallel_load));
  assert property ((reset && (parallel_load != 3'b000)) |=> shift_reg == 3'b000);

  // Shift operations
  assert property (disable iff (reset)
                   (parallel_load == 3'b000 && shift && control)
                   |=> shift_reg == { $past(shift_reg)[1:0], 1'b0});
  assert property (disable iff (reset)
                   (parallel_load == 3'b000 && shift && !control)
                   |=> shift_reg == {1'b0, $past(shift_reg)[2:1]});
  assert property (disable iff (reset)
                   (parallel_load == 3'b000 && !shift)
                   |=> shift_reg == $past(shift_reg));

  // Adder correctness
  assert property (@cb {cout, sum} == A + B + cin);

  // XOR/output correctness (lower 3 bits used by design)
  assert property (@cb xor_result == (sum[2:0] ^ shift_reg));
  assert property (@cb out == xor_result);

  // Coverage
  cover property (@cb reset ##1 !reset);
  cover property (@cb disable iff (reset) (parallel_load != 3'b000));
  cover property (@cb disable iff (reset) (parallel_load != 3'b000 && shift)); // load wins over shift
  cover property (@cb disable iff (reset) (parallel_load == 3'b000 && shift && control));
  cover property (@cb disable iff (reset) (parallel_load == 3'b000 && shift && !control));
  cover property (@cb cout);
  cover property (@cb !cout);
endmodule

bind ripple_shift ripple_shift_sva u_ripple_shift_sva();