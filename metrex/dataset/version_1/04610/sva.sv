// SVA bind module for butterfly3_16
// Concise, pairwise correctness, cross-consistency, X-checks, and key coverage

module butterfly3_16_sva (butterfly3_16 m);

  // Pack ports for compact generate logic
  wire signed [27:0] I [0:15];
  wire signed [27:0] O [0:15];

  assign I[0]  = m.i_0;   assign I[1]  = m.i_1;   assign I[2]  = m.i_2;   assign I[3]  = m.i_3;
  assign I[4]  = m.i_4;   assign I[5]  = m.i_5;   assign I[6]  = m.i_6;   assign I[7]  = m.i_7;
  assign I[8]  = m.i_8;   assign I[9]  = m.i_9;   assign I[10] = m.i_10;  assign I[11] = m.i_11;
  assign I[12] = m.i_12;  assign I[13] = m.i_13;  assign I[14] = m.i_14;  assign I[15] = m.i_15;

  assign O[0]  = m.o_0;   assign O[1]  = m.o_1;   assign O[2]  = m.o_2;   assign O[3]  = m.o_3;
  assign O[4]  = m.o_4;   assign O[5]  = m.o_5;   assign O[6]  = m.o_6;   assign O[7]  = m.o_7;
  assign O[8]  = m.o_8;   assign O[9]  = m.o_9;   assign O[10] = m.o_10;  assign O[11] = m.o_11;
  assign O[12] = m.o_12;  assign O[13] = m.o_13;  assign O[14] = m.o_14;  assign O[15] = m.o_15;

  // Functional mapping per butterfly pair (k, 15-k)
  genvar k;
  generate
    for (k = 0; k < 8; k++) begin : G_PAIR
      always_comb begin
        if (! $isunknown({m.enable, I[k], I[15-k]})) begin
          // Core correctness: pass-through vs sum/diff
          assert (
              ( m.enable && (O[k]     == (I[k] + I[15-k]))
                        && (O[15-k] == (I[k] - I[15-k])) )
           || ( !m.enable && (O[k]     == I[k])
                          && (O[15-k] == I[15-k]) )
          ) else $error("butterfly3_16 pair %0d mapping failed", k);

          // Cross-consistency identities when enabled
          if (m.enable) begin
            assert ( (O[k] + O[15-k]) == (I[k]     <<< 1) )
              else $error("butterfly3_16 sum identity failed for pair %0d", k);
            assert ( (O[k] - O[15-k]) == (I[15-k]  <<< 1) )
              else $error("butterfly3_16 diff identity failed for pair %0d", k);
          end
        end

        // Coverage: both arithmetic overflow cases (signed) and symmetry patterns
        cover ( m.enable
                && (I[k][27] == I[15-k][27])
                && ((I[k] + I[15-k])[27] != I[k][27]) ); // add overflow
        cover ( m.enable
                && (I[k][27] != I[15-k][27])
                && ((I[k] - I[15-k])[27] == I[15-k][27]) ); // sub overflow
        cover ( m.enable && (I[k] ==  I[15-k]) );  // symmetric inputs
        cover ( m.enable && (I[k] == -I[15-k]) );  // anti-symmetric inputs
      end
    end
  endgenerate

  // No-X on outputs when inputs and enable are known
  always_comb begin
    if (! $isunknown({m.enable,
                      I[0], I[1], I[2], I[3], I[4], I[5], I[6], I[7],
                      I[8], I[9], I[10], I[11], I[12], I[13], I[14], I[15]})) begin
      assert (! $isunknown({O[0], O[1], O[2], O[3], O[4], O[5], O[6], O[7],
                            O[8], O[9], O[10], O[11], O[12], O[13], O[14], O[15]}))
        else $error("butterfly3_16 produced X/Z on outputs");
    end

    // Basic enable coverage
    cover (m.enable == 1'b0);
    cover (m.enable == 1'b1);
  end

endmodule

bind butterfly3_16 butterfly3_16_sva sva();