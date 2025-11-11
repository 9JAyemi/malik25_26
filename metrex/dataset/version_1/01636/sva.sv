// SVA checker for twos_complement
module twos_complement_sva #(parameter int WIDTH = 4)
(
  input logic [WIDTH-1:0] binary,
  input logic [WIDTH-1:0] twos_comp
);
  localparam logic [WIDTH-1:0] ONE      = {{(WIDTH-1){1'b0}},1'b1};
  localparam logic [WIDTH-1:0] MASK     = {WIDTH{1'b1}};
  localparam logic [WIDTH-1:0] MOST_NEG = (1'b1 << (WIDTH-1));

  // Core functional checks (immediate assertions; evaluated on any change)
  always_comb begin
    if (!$isunknown(binary)) begin
      // Definition equivalence
      assert (twos_comp == (~binary + ONE))
        else $error("twos_comp mismatch: bin=%0h exp=%0h got=%0h", binary, (~binary + ONE), twos_comp);

      // Modular sum == 0 (mod 2^WIDTH)
      assert ((((binary + twos_comp) & MASK) == '0))
        else $error("sum!=0 mod 2^%0d: bin=%0h twc=%0h", WIDTH, binary, twos_comp);

      // Involution: ~~x + 1 twice -> x
      assert (((((~twos_comp) + ONE) & MASK) == binary))
        else $error("double two's complement != input: bin=%0h twc=%0h", binary, twos_comp);

      // Zero maps to zero (and only zero)
      assert ((binary == '0) == (twos_comp == '0))
        else $error("zero mapping violated: bin=%0h twc=%0h", binary, twos_comp);

      // Most negative is self-inverse
      if (binary == MOST_NEG)
        assert (twos_comp == MOST_NEG)
          else $error("most negative not self-inverse: twc=%0h", twos_comp);

      // No X/Z on output when input is known
      assert (!$isunknown(twos_comp))
        else $error("X/Z on twos_comp for known input: bin=%0h twc=%0h", binary, twos_comp);
    end
  end

  // Coverage: hit all input values and key corner cases
  genvar i;
  generate
    for (i = 0; i < (1<<WIDTH); i++) begin : C_ALL_INPUTS
      always_comb cover (binary == logic'(i[WIDTH-1:0]));
    end
  endgenerate

  always_comb begin
    cover ((binary == '0) && (twos_comp == '0));           // zero case
    cover ((binary == MOST_NEG) && (twos_comp == MOST_NEG)); // most negative self-inverse
    cover ((((binary + twos_comp) & MASK) == '0));         // modular-sum property observed
  end
endmodule

// Bind the checker to the DUT
bind twos_complement twos_complement_sva #(.WIDTH(4))
  i_twos_complement_sva(.binary(binary), .twos_comp(twos_comp));