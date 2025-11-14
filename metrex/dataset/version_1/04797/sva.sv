// SVA checker for sel_to_out. Bind this to the DUT.
module sel_to_out_sva(input logic [3:0] SEL, input logic [7:0] OUT);

  function automatic logic [7:0] exp_out(input logic [3:0] sel);
    logic [7:0] exp;
    if (sel <= 4'd7)       exp = 8'h01 << sel;
    else if (sel == 4'd8)  exp = 8'h00;
    else                   exp = ~((8'h01 << (sel - 4'd9)) - 8'h01);
    return exp;
  endfunction

  // Core mapping check + sanity
  always_comb begin
    assert (#0 (OUT == exp_out(SEL)))
      else $error("sel_to_out map mismatch: SEL=%0h OUT=%0h exp=%0h", SEL, OUT, exp_out(SEL));
    assert (#0 !$isunknown(SEL))
      else $error("SEL has X/Z: %0h", SEL);
    assert (#0 !$isunknown(OUT))
      else $error("OUT has X/Z: %0h", OUT);

    if (SEL <= 4'd7)
      assert (#0 $onehot(OUT))
        else $error("OUT not onehot for SEL=%0h: OUT=%0b", SEL, OUT);
    if (SEL == 4'd8)
      assert (#0 OUT == 8'h00)
        else $error("OUT not 0 for SEL=8: %0h", OUT);
    if (SEL == 4'd9)
      assert (#0 OUT == 8'hFF)
        else $error("OUT not FF for SEL=9: %0h", OUT);
    if (SEL >= 4'd10)
      assert (#0 OUT == ~((8'h01 << (SEL - 4'd9)) - 8'h01))
        else $error("OUT bad prefix-ones for SEL=%0h: OUT=%0b", SEL, OUT);
  end

  // Functional coverage: each SEL value produces its exact expected OUT
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cv
      always_comb cover (SEL == i[3:0] && OUT == exp_out(i[3:0]));
    end
  endgenerate

  // Class coverage for behavior types
  always_comb begin
    cover (SEL <= 4'd7  && $onehot(OUT));
    cover (SEL == 4'd8  && OUT == 8'h00);
    cover (SEL == 4'd9  && OUT == 8'hFF);
    cover (SEL >= 4'd10 && OUT == ~((8'h01 << (SEL - 4'd9)) - 8'h01));
  end

endmodule

bind sel_to_out sel_to_out_sva sva_inst (.*);