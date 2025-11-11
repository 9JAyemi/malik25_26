// SVA binders for the given design (concise, combinational, high-signal-coverage)

module multiplier_module_sva;
  // Check result magnitude and sign; flag Xs; basic scenario coverage
  always @* begin
    automatic logic [15:0] p = a * b;

    if (!$isunknown({a,b})) begin
      assert (result === p)
        else $error("multiplier: result != a*b (a=%0h b=%0h exp=%0h got=%0h)", a,b,p,result);

      assert (sign === (a[7] ^ b[7]))
        else $error("multiplier: sign != a[7]^b[7] (a[7]=%0b b[7]=%0b sign=%0b)", a[7],b[7],sign);

      assert (!$isunknown({result,sign}))
        else $error("multiplier: X/Z on outputs");
    end

    // Functional coverage
    cover ((a[7]==0)&&(b[7]==0));
    cover ((a[7]==1)&&(b[7]==1));
    cover ((a[7]^b[7])==1);
    cover (p==16'h0000);
    cover (p[15]==1'b1);
  end
endmodule

module ripple_carry_adder_sva;
  // Check 4-bit sum behavior and (internal) carry computation; flag Xs
  always @* begin
    automatic logic [4:0] full = a + b + carry_in;

    if (!$isunknown({a,b,carry_in})) begin
      assert (sum === full[3:0])
        else $error("rca: sum mismatch (a=%0h b=%0h cin=%0b exp=%0h got=%0h)",
                    a,b,carry_in,full[3:0],sum);

      // Internal carry_out should reflect overflow of 4-bit add
      assert (carry_out === full[4])
        else $error("rca: carry_out mismatch (a=%0h b=%0h cin=%0b exp=%0b got=%0b)",
                    a,b,carry_in,full[4],carry_out);

      assert (!$isunknown({sum,carry_out}))
        else $error("rca: X/Z on outputs");
    end

    // Functional coverage
    cover (full[4]==1'b1);   // overflow
    cover (sum==4'h0);
    cover (sum==4'hF);
  end
endmodule

module absolute_value_module_sva;
  // Check true absolute value over 5-bit two's complement; flag Xs
  always @* begin
    automatic logic signed [4:0] s = input_sum;
    automatic logic [4:0] abs_exp = (s < 0) ? -s : s;

    if (!$isunknown(input_sum)) begin
      assert (output_abs === abs_exp)
        else $error("abs: mismatch (in=%0b exp=%0b got=%0b)", input_sum, abs_exp, output_abs);

      assert (!$isunknown(output_abs))
        else $error("abs: X/Z on output");
    end

    // Functional coverage
    cover (input_sum[4]==1'b1);     // negative input
    cover (input_sum==5'b10000);    // -16 corner (two's comp min)
    cover (output_abs==5'd0);
    cover (output_abs==5'd16);
  end
endmodule

module top_module_sva;
  // Top-level integration checks and end-to-end equivalence; flag Xs
  always @* begin
    // Expectation for sum_abs from mult_result[15] and adder_result
    automatic logic [4:0] abs_in   = {mult_result[15], adder_result};
    automatic logic [4:0] abs_exp  = abs_in[4] ? (~abs_in + 5'd1) : abs_in;

    // Final result expectation (note 9->8 truncation)
    automatic logic [8:0] abs_shift9 = {sum_abs, 4'b0};
    automatic logic [8:0] neg9       = (~abs_shift9) + 9'd1;
    automatic logic [7:0] final_exp  = mult_sign ? neg9[7:0] : abs_shift9[7:0];

    if (!$isunknown({a,b,adder_result,mult_result,mult_sign,sum_abs})) begin
      // Cross-check submodule behaviors seen at top
      assert (adder_result === ((a[3:0] + b[3:0]) & 4'hF))
        else $error("top: adder_result mismatch");

      assert (sum_abs === abs_exp)
        else $error("top: sum_abs mismatch vs abs(mult_result[15]:adder_result)");

      assert (final_result === final_exp)
        else $error("top: final_result mismatch");

      assert (!$isunknown(final_result))
        else $error("top: X/Z on final_result");
    end

    // Functional coverage across key control/data interactions
    cover (mult_sign==1'b0);
    cover (mult_sign==1'b1);
    cover (mult_result[15]==1'b1);          // abs input negative
    cover (sum_abs==5'd16);                  // max magnitude into shift
    cover (final_result==8'h00);
  end
endmodule

// Bind all SVA modules to DUTs
bind multiplier_module     multiplier_module_sva mult_mod_sva_b ();
bind ripple_carry_adder    ripple_carry_adder_sva rca_sva_b ();
bind absolute_value_module absolute_value_module_sva abs_sva_b ();
bind top_module            top_module_sva top_sva_b ();