// SVA for decoder_3to8
// Active-low one-cold 3:8 decode, combinational, no X/Z, full code coverage.

module decoder_3to8_sva (
  input A, B, C,
  input Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7
);
  wire [2:0] sel = {A,B,C};
  wire [7:0] Y   = {Y7,Y6,Y5,Y4,Y3,Y2,Y1,Y0};

  // No X/Z on inputs/outputs
  a_no_x_in:  assert property (@(A or B or C) !$isunknown(sel));
  a_no_x_out: assert property (@(A or B or C or Y0 or Y1 or Y2 or Y3 or Y4 or Y5 or Y6 or Y7) !$isunknown(Y));

  // Functional decode: active-low one-cold equals ~(1<<sel), with zero-time settle
  a_eq:       assert property (@(A or B or C) ##0 (Y == ~(8'b1 << sel)));

  // Structural sanity: exactly one output low
  a_onecold:  assert property (@(A or B or C or Y0 or Y1 or Y2 or Y3 or Y4 or Y5 or Y6 or Y7) $onehot(~Y));

  // Purely combinational: if inputs hold, outputs hold
  a_stable:   assert property (@(A or B or C or Y0 or Y1 or Y2 or Y3 or Y4 or Y5 or Y6 or Y7) $stable(sel) |-> $stable(Y));

  // Coverage: hit all 8 codes with matching output pattern
  genvar k;
  generate
    for (k=0; k<8; k++) begin : CODES
      c_code: cover property (@(A or B or C) (sel==k) && (Y == ~(8'b1 << k)));
    end
  endgenerate
endmodule

bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva (.*);