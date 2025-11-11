// SVA for decoder — concise, bindable, full functional checks and coverage

// Bind this checker to the DUT:
// bind decoder decoder_sva i_decoder_sva(.in(in), .enable(enable), .out(out));

checker decoder_sva (input logic [2:0] in,
                     input logic       enable,
                     input logic [7:0] out);

  // Expected decode function
  function automatic logic [7:0] exp_out (logic [2:0] i, logic en);
    return en ? (8'b1 << i) : 8'b0;
  endfunction

  // Exact functional mapping on any input change (guarded for known inputs)
  property p_map_known;
    @(in or enable)
      !$isunknown({in,enable}) |-> ##0 (out == exp_out(in, enable));
  endproperty
  assert property (p_map_known);

  // When enable is 0, output must be zero (even if in is X)
  assert property (@(in or enable) (enable === 1'b0) |-> ##0 (out == 8'b0));

  // When enable is 1 and in has any X/Z, case default must drive zero
  assert property (@(in or enable) (enable === 1'b1 && $isunknown(in)) |-> ##0 (out == 8'b0));

  // One-hot output when enabled with known input
  assert property (@(in or enable)
                   (enable === 1'b1 && !$isunknown(in)) |-> ##0 $onehot(out));

  // Output is always known after a driving event
  assert property (@(in or enable) 1'b1 |-> ##0 !$isunknown(out));

  // Output value is always in the legal set {0, power-of-two}
  assert property (@(in or enable)
                   1'b1 |-> ##0 (out == 8'b0 || $onehot(out)));

  // Functional coverage: each decode line and disable case
  genvar gi;
  for (gi = 0; gi < 8; gi++) begin : C_DEC
    cover property (@(in or enable)
                    (enable === 1'b1 && in == gi) ##0 (out == (8'b1 << gi)));
  end
  cover property (@(in or enable) (enable === 1'b0) ##0 (out == 8'b0));

endchecker

bind decoder decoder_sva i_decoder_sva(.in(in), .enable(enable), .out(out));