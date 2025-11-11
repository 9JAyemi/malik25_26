// SVA for bitwise_op. Uses ##0/observed-region checks to avoid NB-<= races.
module bitwise_op_sva (
  input  [15:0] in1, in2, in3, in4,
  input         reset,
  input  [15:0] out1, out2
);

  // Inputs must be known
  assert property (@(in1 or in2 or in3 or in4 or reset)
                   !$isunknown({reset,in1,in2,in3,in4}))
    else $error("bitwise_op: X/Z on inputs");

  // Outputs must be known after settle
  assert property (@(in1 or in2 or in3 or in4 or reset)
                   ##0 !$isunknown({out1,out2}))
    else $error("bitwise_op: X/Z on outputs");

  // Functional correctness (after delta-cycle settle)
  assert property (@(in1 or in2 or in3 or in4 or reset)
                   1 |-> ##0 ( reset
                               ? (out1 === 16'h0000 && out2 === 16'h0000)
                               : (out1 === (in1 & in2) && out2 === (in3 ^ in4)) ))
    else $error("bitwise_op: functional mismatch");

  // Basic coverage
  cover property (@(posedge reset) reset);
  cover property (@(negedge reset) !reset);

  // Output value space under !reset
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out1 == 16'h0000));
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out1 != 16'h0000));
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out2 == 16'h0000)); // implies in3==in4
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out2 != 16'h0000));
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out1 == 16'hFFFF)); // strong-AND case
  cover property (@(in1 or in2 or in3 or in4 or reset) !reset ##0 (out2 == 16'hFFFF)); // full-ones XOR

  // Both outputs non-zero simultaneously under !reset
  cover property (@(in1 or in2 or in3 or in4 or reset)
                  !reset ##0 ((out1 != 16'h0000) && (out2 != 16'h0000)));

endmodule

bind bitwise_op bitwise_op_sva u_bitwise_op_sva (.*);