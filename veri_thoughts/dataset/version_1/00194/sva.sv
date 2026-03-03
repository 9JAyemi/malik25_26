// SVA checker bound into top_module
module top_module_sva
  (input  logic [7:0]  in_hi,
   input  logic [7:0]  in_lo,
   input  logic [16:0] out,
   input  logic [15:0] half_word,
   input  logic        parity_bit);

  // X/Z checks
  always_comb begin
    assert (!$isunknown({in_hi,in_lo})) else $error("X/Z on inputs");
    assert (!$isunknown(out))           else $error("X/Z on out");
  end

  // Functional correctness
  always_comb begin
    assert (half_word == {in_hi, in_lo})      else $error("half_word != {in_hi,in_lo}");
    assert (parity_bit == ^half_word)         else $error("parity_bit != ^half_word");
    assert (out == {half_word, parity_bit})   else $error("out != {half_word,parity_bit}");
  end

  // Coverage (key patterns and both parity classes)
  always_comb begin
    cover (^({in_hi,in_lo}) == 1'b0);         // even parity
    cover (^({in_hi,in_lo}) == 1'b1);         // odd parity
    cover ({in_hi,in_lo} == 16'h0000);
    cover ({in_hi,in_lo} == 16'hFFFF);
    cover ({in_hi,in_lo} == 16'hAAAA);
    cover ({in_hi,in_lo} == 16'h5555);
  end
endmodule

bind top_module top_module_sva sva_i (.*);