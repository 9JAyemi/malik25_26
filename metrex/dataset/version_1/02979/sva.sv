// SVA for custom_or3 – bind into DUT scope and check structure, functionality, and X/Z issues

module custom_or3_sva;
  // Combinational safety and functional checks
  always_comb begin
    // No X/Z on IOs and internal nets
    assert (!$isunknown({A,B,C_N})) else $error("custom_or3: Inputs contain X/Z");
    assert (!$isunknown({w1,w2,w3,w4,w5,w6,w7,w8,X})) else $error("custom_or3: Internal/Output contain X/Z");

    // Structural gate checks
    assert (w2 === (A  | w1 | C_N)) else $error("custom_or3: w2 mismatch");
    assert (w3 === (w1 | B  | C_N)) else $error("custom_or3: w3 mismatch");
    assert (w4 === (w1 | C_N))      else $error("custom_or3: w4 mismatch");
    assert (w5 === (A  | B  | w1))  else $error("custom_or3: w5 mismatch");
    assert (w6 === (A  | w1))       else $error("custom_or3: w6 mismatch");
    assert (w7 === (w1 | B))        else $error("custom_or3: w7 mismatch");
    assert (w8 === w1)              else $error("custom_or3: w8 mismatch");

    // Consistent driving of X: matches both logic paths
    assert (X  === (A | B | C_N))   else $error("custom_or3: X != A|B|C_N");
    assert (X  === w8)              else $error("custom_or3: X != w8");
    assert (w8 === (A | B | C_N))   else $error("custom_or3: path mismatch (w8 vs A|B|C_N)");
  end

  // Coverage: all input combinations, output values, and internal key states
  always_comb begin
    cover ({A,B,C_N} == 3'b000);
    cover ({A,B,C_N} == 3'b001);
    cover ({A,B,C_N} == 3'b010);
    cover ({A,B,C_N} == 3'b011);
    cover ({A,B,C_N} == 3'b100);
    cover ({A,B,C_N} == 3'b101);
    cover ({A,B,C_N} == 3'b110);
    cover ({A,B,C_N} == 3'b111);
    cover (X  == 1'b0);
    cover (X  == 1'b1);
    cover (w1 == 1'b0);
    cover (w1 == 1'b1);
  end
endmodule

bind custom_or3 custom_or3_sva sva_inst();