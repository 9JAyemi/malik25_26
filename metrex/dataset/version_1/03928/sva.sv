// SVA for barrel_shift_mux
// Bind this to the DUT; assertions are immediate (combinational) and concise.

module barrel_shift_mux_sva (
  input logic [31:0] A, B, C, D,
  input logic [4:0]  shift_amount,
  input logic        SEL0, SEL1,
  input logic [31:0] Y
);

  // Functional correctness: Y == selected_input shifted as per RTL
  always_comb begin
    automatic logic [31:0] sel_exp;
    automatic bit          valid_sel = !$isunknown({SEL1,SEL0});
    automatic bit          valid_amt = !$isunknown(shift_amount);

    unique case ({SEL1,SEL0})
      2'b00: sel_exp = A;
      2'b01: sel_exp = B;
      2'b10: sel_exp = C;
      2'b11: sel_exp = D;
      default: sel_exp = 'x;
    endcase

    if (valid_sel && valid_amt) begin
      if (shift_amount != 0)
        assert (Y === (sel_exp << shift_amount))
          else $error("barrel_shift_mux: Y != selected_input << shift_amount");
      else begin
        assert (Y === sel_exp)
          else $error("barrel_shift_mux: Y != selected_input when shift_amount==0");
        // strengthen zero-shift behavior
        assert (Y === (sel_exp << 0));
        assert (Y === (sel_exp >> 0));
      end
    end
  end

  // No unknowns on Y when all drivers are known
  always_comb begin
    if (!$isunknown({A,B,C,D,SEL0,SEL1,shift_amount}))
      assert (!$isunknown(Y))
        else $error("barrel_shift_mux: Y has X/Z with known inputs/select/amount");
  end

  // Coverage: exercise all selects and key shift amounts
  always_comb begin
    automatic bit valid_sel = !$isunknown({SEL1,SEL0});
    automatic bit valid_amt = !$isunknown(shift_amount);
    cover (valid_sel && {SEL1,SEL0} == 2'b00);
    cover (valid_sel && {SEL1,SEL0} == 2'b01);
    cover (valid_sel && {SEL1,SEL0} == 2'b10);
    cover (valid_sel && {SEL1,SEL0} == 2'b11);
    cover (valid_amt && shift_amount == 0);
    cover (valid_amt && shift_amount == 1);
    cover (valid_amt && shift_amount == 31);
    // observable activity on Y edges
    cover (!$isunknown(Y) && (Y[31] || Y[0]));
  end

endmodule

bind barrel_shift_mux barrel_shift_mux_sva sva (
  .A(A), .B(B), .C(C), .D(D),
  .shift_amount(shift_amount),
  .SEL0(SEL0), .SEL1(SEL1),
  .Y(Y)
);