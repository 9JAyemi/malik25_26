// SVA for Adder. Bind this to the DUT.
// Focus: functional correctness, X-prop on known inputs, basic scenario coverage, independence from din_c.

module Adder_sva(input logic [3:0] din_a, din_b, din_c, dout);

  // Functional check (includes truncation) + X check
  always_comb begin
    automatic logic [4:0] s = din_a + din_b;
    assert #0 (dout === s[3:0])
      else $error("Adder mismatch: a=%0h b=%0h exp=%0h got=%0h t=%0t", din_a, din_b, s[3:0], dout, $time);

    if (!$isunknown({din_a, din_b}))
      assert #0 (!$isunknown(dout))
        else $error("Adder X/Z on dout with known inputs: a=%0h b=%0h t=%0t", din_a, din_b, $time);

    // Compact functional coverage
    cover (din_a==4'h0 && din_b==4'h0 && dout==4'h0);          // 0+0
    cover ((s>5'd15) && (dout==s[3:0]));                        // overflow case observed
    cover ((din_b==4'h0) && (dout==din_a));                     // add zero (b)
    cover ((din_a==4'h0) && (dout==din_b));                     // add zero (a)
    cover ((din_a==4'hF) && (din_b==4'hF) && dout==4'hE);       // 15+15=30 -> 14
  end

  // Independence: dout must not change when only din_c changes (a,b stable)
  logic [3:0] a_q, b_q, c_q, y_q;
  initial begin a_q='x; b_q='x; c_q='x; y_q='x; end
  always @(din_a or din_b or din_c or dout) begin
    if ((din_a===a_q) && (din_b===b_q) && (din_c!==c_q))
      assert (dout===y_q)
        else $error("Adder dout changed when only din_c toggled: c %0h->%0h, y %0h->%0h", c_q, din_c, y_q, dout);
    a_q <= din_a; b_q <= din_b; c_q <= din_c; y_q <= dout;
  end

endmodule

bind Adder Adder_sva adder_sva_i(.*);