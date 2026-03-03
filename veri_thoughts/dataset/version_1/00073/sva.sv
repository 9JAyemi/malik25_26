// SVA checker for db_lut_beta
module db_lut_beta_sva (input logic [5:0] qp_i, input logic [6:0] beta_o);

  // Combinational immediate checks and covers
  always_comb begin
    // No X/Z on output when input is known
    if (!$isunknown(qp_i)) assert (!$isunknown(beta_o))
      else $error("db_lut_beta: beta_o X/Z when qp_i known");

    // Golden functional mapping (complete domain 0..63)
    assert ( beta_o ==
             ((qp_i < 6'd16 || qp_i > 6'd51) ? 7'd0
              : (qp_i <= 6'd28) ? ({1'b0,qp_i} - 7'd10)
                                 : (({1'b0,qp_i}<<1) - 7'd38)) )
      else $error("db_lut_beta: mapping mismatch qp_i=%0d beta_o=%0d", qp_i, beta_o);

    // Output range safety
    assert (beta_o inside {[7'd0:7'd64]})
      else $error("db_lut_beta: beta_o out of range: %0d", beta_o);

    // Coverage: default regions and key boundaries/corners
    cover (qp_i inside {[6'd0:6'd15]}  && beta_o==7'd0);
    cover (qp_i==6'd16 && beta_o==7'd6);
    cover (qp_i inside {[6'd17:6'd27]});         // mid of first ramp
    cover (qp_i==6'd28 && beta_o==7'd18);
    cover (qp_i==6'd29 && beta_o==7'd20);
    cover (qp_i inside {[6'd30:6'd50]});         // mid of second ramp
    cover (qp_i==6'd51 && beta_o==7'd64);
    cover (qp_i inside {[6'd52:6'd63]}  && beta_o==7'd0);
  end

endmodule

// Bind into DUT
bind db_lut_beta db_lut_beta_sva sva_i (.qp_i(qp_i), .beta_o(beta_o));