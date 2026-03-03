// SVA for bitwise_shift
// Concise, bindable, combinational sampling

module bitwise_shift_sva(input logic [31:0] a, input logic [31:0] y);
  default clocking cb @(*); endclocking

  // Sanity: no X/Z on inputs/outputs
  assert_no_xz:        assert property (!$isunknown({a,y}));

  // Functional equivalence
  func_exact:          assert property (y == (32'd12345 >> a));

  // Key edge behaviors
  zero_ge14:           assert property ((a >= 14) |-> (y == 32'd0));
  nonzero_lt14:        assert property ((a < 14)  |-> (y != 32'd0));
  zero_ge32:           assert property ((a >= 32) |-> (y == 32'd0));
  no_shift_case:       assert property ((a == 0)  |-> (y == 32'd12345));

  // Structural: MSBs must always be zero (operand fits in 14 bits)
  msb_always_zero:     assert property (y[31:14] == '0);

  // Coverage of important cases
  cover_no_shift:      cover property (a == 0  && y == 32'd12345);
  cover_max_nz:        cover property (a == 13 && y == (32'd12345 >> 13));
  cover_first_zero:    cover property (a == 14 && y == 32'd0);
  cover_31:            cover property (a == 31 && y == 32'd0);
  cover_ge32:          cover property (a >= 32 && y == 32'd0);
endmodule

// Bind into DUT
bind bitwise_shift bitwise_shift_sva sva_inst(.a(a), .y(y));