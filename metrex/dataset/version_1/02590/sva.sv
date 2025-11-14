// SVA for TwosComplement
module TwosComplement_sva (input [3:0] input_num, input [3:0] twos_comp);

  // Sample on any combinational change; ignore checks when input has X/Z
  default clocking cb @(*) ; endclocking
  default disable iff ($isunknown(input_num));

  // Functional spec: two's complement
  assert property (twos_comp == (~input_num + 4'd1))
    else $error("TwosComplement spec mismatch: ~input_num+1 != twos_comp");

  // Algebraic invariant: x + (-x) = 1_0000 (5 bits)
  assert property ((input_num + twos_comp) == 5'b1_0000)
    else $error("Sum invariant failed: input_num + twos_comp != 5'b1_0000");

  // Involution: -(-x) = x
  assert property ((~twos_comp + 4'd1) == input_num)
    else $error("Involution failed: ~(twos_comp)+1 != input_num");

  // Output must be known whenever input is known
  assert property (!$isunknown(twos_comp))
    else $error("twos_comp contains X/Z while input_num is known");

  // Corner cases
  assert property ((input_num == 4'd0) |-> (twos_comp == 4'd0))
    else $error("Zero case failed");
  assert property ((input_num == 4'd8) |-> (twos_comp == 4'd8))
    else $error("Min-int case (0x8) failed");

  // Coverage: hit all input values
  generate
    genvar v;
    for (v = 0; v < 16; v++) begin : C_INPUTS
      localparam [3:0] VAL = v;
      cover property (input_num == VAL);
    end
  endgenerate

  // Coverage: corner cases exercised
  cover property (input_num == 4'd0 && twos_comp == 4'd0);
  cover property (input_num == 4'd8 && twos_comp == 4'd8);

endmodule

bind TwosComplement TwosComplement_sva sva_twoscomp (.*);