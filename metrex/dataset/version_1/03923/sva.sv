// SVA checker for LUT_SHIFT
module lut_shift_sva #(parameter int P = 5) (
  input  logic         CLK,
  input  logic         EN_ROM1,
  input  logic  [4:0]  ADRS,
  input  logic  [P-1:0] O_D
);

  // Parameter sanity
  initial assert (P >= 5)
    else $error("LUT_SHIFT: parameter P (%0d) must be >= 5 to preserve 5-bit ROM contents", P);

  // Golden model of the ROM (zero-extended to P bits)
  function automatic logic [P-1:0] exp_lut (input logic [4:0] a);
    logic [4:0] e;
    if      (a <= 5'd3)   e = a + 5'd1;
    else if (a <= 5'd13)  e = a;
    else                  e = a - 5'd1; // 14..31
    return {{(P-5){1'b0}}, e};
  endfunction

  // On enable with known address, next-cycle O_D matches ROM
  property p_update_known;
    @(posedge CLK) EN_ROM1 && !$isunknown(ADRS) |=> O_D == exp_lut(ADRS);
  endproperty
  assert property (p_update_known);

  // On enable with unknown address, default branch drives zero next cycle
  property p_update_unknown_default;
    @(posedge CLK) EN_ROM1 && $isunknown(ADRS) |=> O_D == '0;
  endproperty
  assert property (p_update_unknown_default);

  // When disabled, output holds its previous value
  property p_hold_when_disabled;
    @(posedge CLK) !EN_ROM1 |=> $stable(O_D);
  endproperty
  assert property (p_hold_when_disabled);

  // Optional: O_D upper bits remain zero on any enabled update (for P>5)
  property p_zero_extend_on_enable;
    @(posedge CLK) EN_ROM1 && !$isunknown(ADRS) |=> O_D[P-1:5] == '0;
  endproperty
  assert property (p_zero_extend_on_enable);

  // Coverage: hit every address and observe correct update
  genvar a;
  generate
    for (a = 0; a < 32; a++) begin : C_ADDR
      cover property (@(posedge CLK) EN_ROM1 && ADRS == a[4:0] |=> O_D == exp_lut(a[4:0]));
    end
  endgenerate

  // Coverage: see hold behavior
  cover property (@(posedge CLK) !EN_ROM1 |=> $stable(O_D));

  // Coverage: see default-on-unknown address
  cover property (@(posedge CLK) EN_ROM1 && $isunknown(ADRS) |=> O_D == '0);

endmodule

// Bind into the DUT
bind LUT_SHIFT lut_shift_sva #(.P(P)) lut_shift_sva_i (
  .CLK(CLK), .EN_ROM1(EN_ROM1), .ADRS(ADRS), .O_D(O_D)
);