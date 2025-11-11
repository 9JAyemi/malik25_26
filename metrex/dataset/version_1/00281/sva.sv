// SVA checker for mux4to1
// Binds directly to the DUT (no clock/reset required). Focuses on
// correctness, X-safety, and concise functional coverage.

module mux4to1_sva(input logic A,B,C,D,S0,S1,Y);
  // Golden 4:1 mux function
  logic golden_y;
  always_comb golden_y = (S1 ? (S0 ? D : C) : (S0 ? B : A));

  // Assertions and coverage fire only when all controls/data are known
  always_comb begin
    if (!$isunknown({A,B,C,D,S0,S1})) begin
      // Functional correctness (will FAIL for the given implementation if it’s not a true 4:1 mux)
      assert (Y === golden_y)
        else $error("mux4to1 functional mismatch: Y=%0b expected=%0b sel={S1,S0}=%0b%0b A=%0b B=%0b C=%0b D=%0b",
                    Y, golden_y, S1, S0, A,B,C,D);

      // Deterministic output when inputs are known
      assert (!$isunknown(Y))
        else $error("mux4to1 output is X/Z with known inputs/selects");
    end

    // Basic input/select sanity (flag X/Z on controls/data)
    assert (!$isunknown({S0,S1}))
      else $error("mux4to1 select lines contain X/Z");
    assert (!$isunknown({A,B,C,D}))
      else $error("mux4to1 data inputs contain X/Z");

    // Functional coverage: each select combo selects the correct data
    cover (!$isunknown({A,B,C,D,S0,S1}) && {S1,S0}==2'b00 && Y===A);
    cover (!$isunknown({A,B,C,D,S0,S1}) && {S1,S0}==2'b01 && Y===B);
    cover (!$isunknown({A,B,C,D,S0,S1}) && {S1,S0}==2'b10 && Y===C);
    cover (!$isunknown({A,B,C,D,S0,S1}) && {S1,S0}==2'b11 && Y===D);

    // Bug witness coverage: Y differs from the golden 4:1 mux behavior
    cover (!$isunknown({A,B,C,D,S0,S1}) && (Y !== golden_y));
  end
endmodule

// Bind into all instances of mux4to1
bind mux4to1 mux4to1_sva u_mux4to1_sva (.*);