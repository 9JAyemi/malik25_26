// SVA for sky130_fd_sc_hd__a221o: X = (A1&A2) | (B1&B2) | C1
// Bind this into the DUT
module sky130_fd_sc_hd__a221o_sva;

  // Functional and structural equivalence when inputs are all known
  always_comb begin
    bit known_in = !$isunknown({A1,A2,B1,B2,C1});
    if (known_in) begin
      assert (X === ((A1 & A2) | (B1 & B2) | C1))
        else $error("a221o func mismatch: X=%b exp=%b A1=%b A2=%b B1=%b B2=%b C1=%b",
                    X, ((A1 & A2) | (B1 & B2) | C1), A1,A2,B1,B2,C1);
      assert (and1_out === (A1 & A2)) else $error("and1_out != A1&A2");
      assert (and0_out === (B1 & B2)) else $error("and0_out != B1&B2");
      assert (or0_out_X === (and1_out | and0_out | C1)) else $error("or0_out_X != and1|and0|C1");
      assert (X === or0_out_X) else $error("X != or0_out_X");
      assert (!$isunknown(X)) else $error("X is X/Z with known inputs");
    end
  end

  // C1 dominance should always force X=1
  always_comb if (C1 === 1'b1) assert (X === 1'b1) else $error("C1=1 must force X=1");

  // All-zero inputs must force X=0
  always_comb if ({A1,A2,B1,B2,C1} === 5'b00000) assert (X === 1'b0) else $error("all zero -> X must be 0");

  // Coverage: each single term independently drives X high
  cover property (@(posedge X) (C1===1'b0) && (A1 & A2) && !(B1 & B2));
  cover property (@(posedge X) (C1===1'b0) && (B1 & B2) && !(A1 & A2));
  cover property (@(posedge X) (C1===1'b1) && !(A1 & A2) && !(B1 & B2));

  // Coverage: X low when all terms low
  cover property (@(negedge X) !(A1 & A2) && !(B1 & B2) && (C1===1'b0));

  // Toggle coverage for internals and output
  cover property (@(posedge and1_out));
  cover property (@(negedge and1_out));
  cover property (@(posedge and0_out));
  cover property (@(negedge and0_out));
  cover property (@(posedge X));
  cover property (@(negedge X));

endmodule

bind sky130_fd_sc_hd__a221o sky130_fd_sc_hd__a221o_sva a221o_sva_i();