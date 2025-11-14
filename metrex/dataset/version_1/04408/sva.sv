// SVA checker for unsigned_sqrt
module unsigned_sqrt_sva (input logic [3:0] num, input logic [3:0] sqrt);

  // Reference model: floor(sqrt(num)) for 0..15
  function automatic logic [3:0] isqrt4 (input logic [3:0] x);
    if (x >= 4'd9)      return 4'd3;
    else if (x >= 4'd4) return 4'd2;
    else if (x >= 4'd1) return 4'd1;
    else                return 4'd0;
  endfunction

  // Core checks (combinational)
  always @* begin
    if (!$isunknown(num)) begin
      // No X/Z on output
      assert (!$isunknown(sqrt))
        else $error("unsigned_sqrt: sqrt has X/Z for num=%0d", num);

      // Exact functional equivalence to spec
      assert (sqrt == isqrt4(num))
        else $error("unsigned_sqrt: mismatch num=%0d exp=%0d got=%0d",
                    num, isqrt4(num), sqrt);

      // Mathematical floor property (redundant cross-check, width-safe)
      int unsigned num_i = num;
      int unsigned s_i   = sqrt;
      assert (s_i*s_i <= num_i && num_i < (s_i+1)*(s_i+1))
        else $error("unsigned_sqrt: floor property fail num=%0d sqrt=%0d",
                    num, sqrt);
    end
  end

  // Functional coverage: exercise all inputs and observe correct output
  cover property (@(*) sqrt == isqrt4(num));

  genvar k;
  generate
    for (k = 0; k < 16; k++) begin : C_NUMS
      cover property (@(*) (num == k[3:0]) && (sqrt == isqrt4(k[3:0])));
    end
  endgenerate

endmodule

// Bind into DUT
bind unsigned_sqrt unsigned_sqrt_sva u_unsigned_sqrt_sva (.num(num), .sqrt(sqrt));