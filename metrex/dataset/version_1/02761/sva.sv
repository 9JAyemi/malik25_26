// SVA for bcd_to_binary
// Binds combinational checks and coverage to the DUT without modifying it.

module bcd_to_binary_sva (
  input [3:0] bcd0,
  input [3:0] bcd1,
  input [3:0] bcd2,
  input [3:0] bcd3,
  input [3:0] bin
);

  function automatic int unsigned dec_from_bcd(input [3:0] d0, d1, d2, d3);
    return d3*1000 + d2*100 + d1*10 + d0;
  endfunction

  wire valid_digits = (bcd0 <= 9) && (bcd1 <= 9) && (bcd2 <= 9) && (bcd3 <= 9);
  wire no_x         = !$isunknown({bcd3,bcd2,bcd1,bcd0,bin});
  wire [3:0] expected = dec_from_bcd(bcd0,bcd1,bcd2,bcd3)[3:0]; // modulo-16 result

  // Immediate (combinational) checks
  always @* begin
    assert (no_x)
      else $error("bcd_to_binary: X/Z on inputs or bin");
    assert (valid_digits)
      else $error("bcd_to_binary: Invalid BCD digit(s): %0d%0d%0d%0d", bcd3,bcd2,bcd1,bcd0);
    assert (!valid_digits || (bin == expected))
      else $error("bcd_to_binary: Mismatch bin=%0d expected(mod16)=%0d", bin, expected);
  end

  // Concurrent coverage on input changes
  // Extremes
  cover property (@(bcd0 or bcd1 or bcd2 or bcd3)
                  valid_digits && (bcd3==0 && bcd2==0 && bcd1==0 && bcd0==0));
  cover property (@(bcd0 or bcd1 or bcd2 or bcd3)
                  valid_digits && (bcd3==9 && bcd2==9 && bcd1==9 && bcd0==9));

  // Exercise all 16 possible bin outputs under valid inputs
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_bin
      cover property (@(bcd0 or bcd1 or bcd2 or bcd3)
                      valid_digits && (bin == i[3:0]));
    end
  endgenerate

endmodule

bind bcd_to_binary bcd_to_binary_sva b2b_sva (.*);