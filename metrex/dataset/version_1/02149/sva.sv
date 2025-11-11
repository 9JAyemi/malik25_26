// SVA checker for priority_encoder/top_module
module pe_sva (input logic [7:0] in, input logic [2:0] pos);

  // Functional equivalence: pos must be bitwise NOT of in[2:0] (with X-propagation)
  always_comb
    assert (pos === ~in[2:0])
      else $error("priority_encoder: pos != ~in[2:0] (pos=%0b, ~in[2:0]=%0b, in=%0h)", pos, ~in[2:0], in);

  // Sanity: if low bits of input are known, output must be known
  always_comb
    if (!$isunknown(in[2:0]))
      assert (!$isunknown(pos))
        else $error("priority_encoder: pos has X/Z while in[2:0] is known (in=%0b pos=%0b)", in, pos);

  // Coverage: hit all 8 values on in[2:0]
  genvar gi;
  generate
    for (gi = 0; gi < 8; gi++) begin : C_LOW3
      localparam logic [2:0] VAL = gi[2:0];
      always_comb cover (in[2:0] == VAL);
    end
  endgenerate

  // Coverage: upper bits extremes, and X on low bits observed
  always_comb cover (in[7:3] == 5'b00000);
  always_comb cover (in[7:3] == 5'b11111);
  always_comb cover ($isunknown(in[2:0]));

endmodule

// Bind the checker to both modules
bind priority_encoder pe_sva pe_sva_dut (.in(in), .pos(pos));
bind top_module        pe_sva pe_sva_top (.in(in), .pos(pos));