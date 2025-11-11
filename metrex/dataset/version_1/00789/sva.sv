// SVA checker for mux_4to1
// Focused, combinational, and concise. Bind this to the DUT.

module mux_4to1_sva (
  input A, B, C, D, S0, S1,
  input Y
);

  // Combinational equivalence to truth table
  always_comb begin
    assert (Y === ((~S0 & ~S1 & A) |
                   (~S0 &  S1 & B) |
                   ( S0 & ~S1 & C) |
                   ( S0 &  S1 & D)))
      else $error("mux_4to1 SVA: Y mismatches truth table");

    // Exactly one minterm active when selects are known
    if (!$isunknown({S0,S1})) begin
      assert ($onehot({~S0 & ~S1, ~S0 & S1, S0 & ~S1, S0 & S1}))
        else $error("mux_4to1 SVA: select minterms not one-hot");
    end

    // If all inputs/selects are known, Y must be known
    if (!$isunknown({A,B,C,D,S0,S1})) begin
      assert (!$isunknown(Y))
        else $error("mux_4to1 SVA: Y is X/Z with all-known inputs");
    end
  end

  // Functional coverage: hit each select combination
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1) (!S1 && !S0));
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1) ( S1 && !S0));
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1) (!S1 &&  S0));
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1) ( S1 &&  S0));

  // Functional coverage: selected input drives Y on its toggle
  cover property (@(posedge A or negedge A) (!S1 && !S0 && !$isunknown({S0,S1,A})) ##0 (Y === A));
  cover property (@(posedge B or negedge B) ( S1 && !S0 && !$isunknown({S0,S1,B})) ##0 (Y === B));
  cover property (@(posedge C or negedge C) (!S1 &&  S0 && !$isunknown({S0,S1,C})) ##0 (Y === C));
  cover property (@(posedge D or negedge D) ( S1 &&  S0 && !$isunknown({S0,S1,D})) ##0 (Y === D));

endmodule

// Bind into the DUT
bind mux_4to1 mux_4to1_sva u_mux_4to1_sva (.A(A), .B(B), .C(C), .D(D), .S0(S0), .S1(S1), .Y(Y));