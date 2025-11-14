// SVA checker for parity_generator
module parity_generator_sva (
  input logic in1,
  input logic in2,
  input logic in3,
  input logic in4,
  input logic parity
);
  wire [3:0] in = {in1,in2,in3,in4};
  wire exp = ^in;

  // Functional correctness (when inputs are known) and zero-delay update on any input change
  a_parity_equals_xor: assert property (@(in1 or in2 or in3 or in4)
                                        !$isunknown(in) |-> ##0 (parity === exp));

  // No spurious parity change without an input change
  a_change_has_cause:  assert property (@(parity) $changed(in));

  // Parity never X/Z when inputs are known
  a_no_x_parity_when_inputs_known: assert property (@(in1 or in2 or in3 or in4)
                                                    !$isunknown(in) |-> !$isunknown(parity));

  // Functional coverage: all 16 input combinations observed with correct parity
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : combo_cov
      localparam logic [3:0] COMBO = v[3:0];
      localparam logic       EXPCT = ^COMBO;
      c_combo: cover property (@(in1 or in2 or in3 or in4)
                               (in == COMBO) && (parity == EXPCT));
    end
  endgenerate

  // Coverage: parity toggles due to some input change
  c_parity_toggle: cover property (@(in1 or in2 or in3 or in4)
                                   parity != $past(parity, 1, @(in1 or in2 or in3 or in4)));
endmodule

// Bind into DUT
bind parity_generator parity_generator_sva sva_i (.*);