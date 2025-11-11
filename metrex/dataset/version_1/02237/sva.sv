// SVA for decoder_3to8
module decoder_3to8_sva (decoder_3to8 dut);

  wire [2:0] ABC = {dut.C, dut.B, dut.A};
  wire [7:0] Y   = {dut.Y7, dut.Y6, dut.Y5, dut.Y4, dut.Y3, dut.Y2, dut.Y1, dut.Y0};

  // Sample on any input/output activity to keep things race-free
  default clocking cb @(
    dut.A or dut.B or dut.C or
    dut.Y0 or dut.Y1 or dut.Y2 or dut.Y3 or dut.Y4 or dut.Y5 or dut.Y6 or dut.Y7
  ); endclocking

  // Sanity: no X/Z on inputs, internal reg, or outputs
  assert property (!$isunknown(ABC));
  assert property (!$isunknown(dut.input_reg));
  assert property (!$isunknown(Y));

  // One-hot correctness of outputs
  assert property ($onehot(Y));

  // Outputs are a pure one-hot decode of the internal input_reg
  assert property (Y == (8'b1 << dut.input_reg));

  // input_reg must capture inputs on the next delta after an input change
  assert property (@(dut.A or dut.B or dut.C) 1 |-> ##0 (dut.input_reg == ABC));

  // Outputs must reflect the inputs on the next delta after an input change
  assert property (@(dut.A or dut.B or dut.C) 1 |-> ##0 (Y == (8'b1 << ABC)));

  // If inputs are stable between samples, outputs must be stable too
  assert property ($stable(ABC) |-> $stable(Y));

  // Coverage: observe all 8 input codes with matching one-hot output
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : COV
      cover property (@(dut.A or dut.B or dut.C) ##0 (ABC == i && Y == (8'b1 << i)));
    end
  endgenerate

endmodule

bind decoder_3to8 decoder_3to8_sva sva();