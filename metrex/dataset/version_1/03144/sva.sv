// SVA checker for clk_select
module clk_select_sva (
  input logic [3:0] inclk,
  input logic [1:0] clkselect,
  input logic       outclk
);

  // Functional equivalence (4-state exact)
  assert property (outclk === inclk[clkselect])
    else $error("clk_select: outclk != inclk[clkselect]");

  // Output may change only if select or the selected input changes
  assert property (
      $changed(outclk) |-> (
           $changed(clkselect)
        || (clkselect==2'b00 && $changed(inclk[0]))
        || (clkselect==2'b01 && $changed(inclk[1]))
        || (clkselect==2'b10 && $changed(inclk[2]))
        || (clkselect==2'b11 && $changed(inclk[3]))
      )
  ) else $error("clk_select: outclk changed without cause");

  // Changes on unselected inputs must not perturb outclk when select is stable
  genvar j;
  generate
    for (j=0; j<4; j++) begin : g_no_side_effects
      assert property ( !$changed(clkselect) && (clkselect != j) && $changed(inclk[j]) |-> !$changed(outclk) )
        else $error("clk_select: unselected inclk[%0d] perturbed outclk", j);
    end
  endgenerate

  // Coverage: each select value exercised with correct mapping
  cover property (clkselect==2'b00 && outclk===inclk[0]);
  cover property (clkselect==2'b01 && outclk===inclk[1]);
  cover property (clkselect==2'b10 && outclk===inclk[2]);
  cover property (clkselect==2'b11 && outclk===inclk[3]);

  // Coverage: outclk changes due to selected input changes
  generate
    for (j=0; j<4; j++) begin : g_cov_sel_input_change
      cover property (clkselect==j && $changed(inclk[j]) && $changed(outclk));
    end
  endgenerate

  // Coverage: outclk updates upon select change
  cover property ($changed(clkselect) && outclk===inclk[clkselect]);

endmodule

// Bind into DUT
bind clk_select clk_select_sva sva_i (.*);