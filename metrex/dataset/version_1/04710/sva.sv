// SVA for circl_s: concise, high-quality functional checking and coverage.
// Assumes a sampling clock is available in the environment.
// Bind the SVA module to the DUT instance(s) as shown at the end.

module circl_s_sva (
  input logic        clk,
  input logic [4:0]  in_addr,
  input logic [4:0]  out_word
);

  default clocking cb @(posedge clk); endclocking

  // Golden mapping function
  function automatic logic [4:0] exp(input logic [4:0] a);
    case (a)
      5'h00: exp = 5'h00;
      5'h01: exp = 5'h05;
      5'h02: exp = 5'h09;
      5'h03: exp = 5'h0B;
      5'h04: exp = 5'h0D;
      5'h05: exp = 5'h0F;
      5'h06: exp = 5'h10;
      5'h07: exp = 5'h12;
      5'h08: exp = 5'h13;
      5'h09: exp = 5'h14;
      5'h0A: exp = 5'h15;
      5'h0B: exp = 5'h16;
      5'h0C: exp = 5'h17;
      5'h0D: exp = 5'h17;
      5'h0E: exp = 5'h18;
      5'h0F: exp = 5'h19;
      5'h10: exp = 5'h19;
      5'h11: exp = 5'h1A;
      5'h12: exp = 5'h1A;
      5'h13: exp = 5'h1B;
      5'h14: exp = 5'h1B;
      5'h15: exp = 5'h1C;
      5'h16: exp = 5'h1C;
      5'h17: exp = 5'h1C;
      5'h18: exp = 5'h1C;
      5'h19: exp = 5'h1D;
      5'h1A: exp = 5'h1D;
      5'h1B: exp = 5'h1D;
      5'h1C: exp = 5'h1D;
      5'h1D: exp = 5'h1D;
      5'h1E: exp = 5'h1D;
      5'h1F: exp = 5'h00;
      default: exp = 'x;
    endcase
  endfunction

  // No X/Z on interface
  a_no_x: assert property (!$isunknown({in_addr, out_word})))
    else $error("circl_s: X/Z detected: in=%0h out=%0h", in_addr, out_word);

  // Pure functional correctness
  a_map: assert property (out_word == exp(in_addr))
    else $error("circl_s: map mismatch: in=%0h out=%0h exp=%0h", in_addr, out_word, exp(in_addr));

  // Sanity invariant independent of the table:
  // For consecutive inputs that increase by +1 (except wrap from 1F),
  // output must be non-decreasing.
  a_monotonic: assert property ( (in_addr == $past(in_addr)+1 && $past(in_addr) != 5'h1F) |-> out_word >= $past(out_word) )
    else $error("circl_s: non-monotonic step: prev_in=%0h prev_out=%0h in=%0h out=%0h",
                $past(in_addr), $past(out_word), in_addr, out_word);

  // Coverage: hit every address with correct mapping
  generate
    genvar i;
    for (i = 0; i < 32; i++) begin : g_cov_all
      c_addr_i: cover property (in_addr == i[4:0] && out_word == exp(i[4:0]));
    end
  endgenerate

  // Coverage: wrap case 1F -> 00 observed
  c_wrap: cover property ($past(in_addr) == 5'h1E && in_addr == 5'h1F && out_word == 5'h00);

  // Coverage: max value reached
  c_max: cover property (out_word == 5'h1D);

endmodule

// Bind example (ensure a clock named 'clk' is visible in the bind scope)
bind circl_s circl_s_sva u_circl_s_sva(.clk(clk), .in_addr(in_addr), .out_word(out_word));