// SVA checker for lab2_part7 and its b2d_7seg instances.
// Bind this checker to the DUT after compilation.

module lab2_part7_sva
(
  input logic [5:0] SW,
  input logic [5:0] LEDR,
  input logic [0:6] HEX1, HEX0,
  input logic [3:0] TENS, ONES
);

  // Combinational, clockless checks and coverage
  always_comb begin
    // Only check when inputs are known
    if (!$isunknown(SW)) begin
      // No X/Z on observable outputs
      assert (!$isunknown({LEDR, HEX1, HEX0})) else $error("X/Z on outputs");

      // Mirror check
      assert (LEDR == SW) else $error("LEDR != SW");

      // Compute expected TENS/ONES
      automatic int sw = SW;
      automatic int exp_tens = (sw > 59)? 6 :
                               (sw > 49)? 5 :
                               (sw > 39)? 4 :
                               (sw > 29)? 3 :
                               (sw > 19)? 2 :
                               (sw >  9)? 1 : 0;
      automatic int exp_ones = sw - exp_tens*10;

      // Range and consistency checks
      assert (TENS <= 6) else $error("TENS out of range");
      assert (ONES <= 9) else $error("ONES out of range");
      assert (TENS == exp_tens) else $error("TENS decode mismatch");
      assert (ONES == exp_ones) else $error("ONES decode mismatch");
      assert (TENS*10 + ONES == sw) else $error("TENS*10+ONES != SW");

      // Inputs to 7-seg are valid decimal digits
      assert (TENS < 10 && ONES < 10) else $error("7-seg input not BCD");

      // Same digit drives same pattern across instances
      if (TENS == ONES) assert (HEX1 == HEX0) else $error("HEX mismatch for equal digits");

      // Branch boundary spot-checks (also double as covers)
      assert (SW==9  -> (TENS==0 && ONES==9 )) else $error("9 boundary wrong");
      assert (SW==10 -> (TENS==1 && ONES==0 )) else $error("10 boundary wrong");
      assert (SW==19 -> (TENS==1 && ONES==9 )) else $error("19 boundary wrong");
      assert (SW==20 -> (TENS==2 && ONES==0 )) else $error("20 boundary wrong");
      assert (SW==29 -> (TENS==2 && ONES==9 )) else $error("29 boundary wrong");
      assert (SW==30 -> (TENS==3 && ONES==0 )) else $error("30 boundary wrong");
      assert (SW==39 -> (TENS==3 && ONES==9 )) else $error("39 boundary wrong");
      assert (SW==40 -> (TENS==4 && ONES==0 )) else $error("40 boundary wrong");
      assert (SW==49 -> (TENS==4 && ONES==9 )) else $error("49 boundary wrong");
      assert (SW==50 -> (TENS==5 && ONES==0 )) else $error("50 boundary wrong");
      assert (SW==59 -> (TENS==5 && ONES==9 )) else $error("59 boundary wrong");
      assert (SW==60 -> (TENS==6 && ONES==0 )) else $error("60 boundary wrong");
      assert (SW==63 -> (TENS==6 && ONES==3 )) else $error("63 boundary wrong");

      // Functional coverage (immediate cover) for key values and ranges
      cover (SW==0);  cover (SW==9);   cover (SW==10); cover (SW==19);
      cover (SW==20); cover (SW==29);  cover (SW==30); cover (SW==39);
      cover (SW==40); cover (SW==49);  cover (SW==50); cover (SW==59);
      cover (SW==60); cover (SW==63);

      // Hit all TENS and ONES digits
      cover (TENS==0); cover (TENS==1); cover (TENS==2); cover (TENS==3);
      cover (TENS==4); cover (TENS==5); cover (TENS==6);
      cover (ONES==0); cover (ONES==1); cover (ONES==2); cover (ONES==3); cover (ONES==4);
      cover (ONES==5); cover (ONES==6); cover (ONES==7); cover (ONES==8); cover (ONES==9);

      // Ensure each segment goes 0 and 1 at least once (both displays)
      foreach (HEX1[i]) begin cover (HEX1[i] == 1'b0); cover (HEX1[i] == 1'b1); end
      foreach (HEX0[i]) begin cover (HEX0[i] == 1'b0); cover (HEX0[i] == 1'b1); end
    end
  end
endmodule

// Bind assertions to DUT (exposes internal TENS/ONES to the checker)
bind lab2_part7 lab2_part7_sva u_lab2_part7_sva (
  .SW(SW), .LEDR(LEDR), .HEX1(HEX1), .HEX0(HEX0), .TENS(TENS), .ONES(ONES)
);