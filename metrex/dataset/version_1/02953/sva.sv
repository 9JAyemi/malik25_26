// SVA for mux4to1
// Bind this checker to the DUT
bind mux4to1 mux4to1_sva u_mux4to1_sva (.Y(Y), .A0(A0), .A1(A1), .A2(A2), .A3(A3), .S0(S0), .S1(S1));

module mux4to1_sva (input logic Y, A0, A1, A2, A3, S0, S1);

  // Truth-table equivalence (avoids X/Z on selects)
  always_comb begin
    if (!$isunknown({S1,S0})) begin
      unique case ({S1,S0})
        2'b00: assert (Y === A0) else $error("mux4to1: Y!=A0 for S=00");
        2'b01: assert (Y === A1) else $error("mux4to1: Y!=A1 for S=01");
        2'b10: assert (Y === A2) else $error("mux4to1: Y!=A2 for S=10");
        2'b11: assert (Y === A3) else $error("mux4to1: Y!=A3 for S=11");
      endcase
    end
  end

  // Sum-of-products structural equivalence when all inputs known
  always_comb begin
    if (!$isunknown({S1,S0,A0,A1,A2,A3})) begin
      logic exp;
      exp = ((~S0 & ~S1 & A0) | (~S0 &  S1 & A1) |
             ( S0 & ~S1 & A2) | ( S0 &  S1 & A3));
      assert (Y === exp) else $error("mux4to1: Y!=SOP expectation");
    end
  end

  // Exactly one product term active when selects are 2-state
  always_comb begin
    if (!$isunknown({S1,S0})) begin
      logic [3:0] en;
      en = {S1&S0, S0&~S1, ~S0&S1, ~S0&~S1}; // {A3,A2,A1,A0}
      assert ($onehot(en)) else $error("mux4to1: product enables not onehot");
    end
  end

  // Coverage: each select combination observed
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1)
                  !$isunknown({S1,S0}) && {S1,S0}==2'b00);
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1)
                  !$isunknown({S1,S0}) && {S1,S0}==2'b01);
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1)
                  !$isunknown({S1,S0}) && {S1,S0}==2'b10);
  cover property (@(posedge S0 or negedge S0 or posedge S1 or negedge S1)
                  !$isunknown({S1,S0}) && {S1,S0}==2'b11);

  // Coverage: selected input change propagates to Y in same cycle (##0 to avoid preponed)
  cover property (@(posedge A0 or negedge A0)
                  (!$isunknown({S1,S0}) && {S1,S0}==2'b00) ##0 (Y===A0));
  cover property (@(posedge A1 or negedge A1)
                  (!$isunknown({S1,S0}) && {S1,S0}==2'b01) ##0 (Y===A1));
  cover property (@(posedge A2 or negedge A2)
                  (!$isunknown({S1,S0}) && {S1,S0}==2'b10) ##0 (Y===A2));
  cover property (@(posedge A3 or negedge A3)
                  (!$isunknown({S1,S0}) && {S1,S0}==2'b11) ##0 (Y===A3));

endmodule