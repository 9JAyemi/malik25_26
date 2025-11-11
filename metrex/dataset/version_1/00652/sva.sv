// SVA for stratixiv_bias_logic
module stratixiv_bias_logic_sva (
  input  logic clk,
  input  logic shiftnld,
  input  logic captnupdt,
  input  logic mainclk,
  input  logic updateclk,
  input  logic capture,
  input  logic update
);

  logic g;
  assign g = (captnupdt | shiftnld);

  // Inputs/outputs must be 0/1 only (avoid default branch via X/Z)
  always_comb begin
    assert #0 (!$isunknown({clk, shiftnld, captnupdt}))
      else $error("X/Z on inputs");
    assert #0 (!$isunknown({mainclk, updateclk, capture, update}))
      else $error("X/Z on outputs");
  end

  // Functional equivalence (combinational, 0-delay check)
  always_comb begin
    assert #0 (mainclk   === (clk & ~g)) else $error("mainclk != clk & ~(captnupdt|shiftnld)");
    assert #0 (updateclk === (clk &  g)) else $error("updateclk != clk &  (captnupdt|shiftnld)");
    assert #0 (capture   ===  captnupdt) else $error("capture != captnupdt");
    assert #0 (update    === ~g)         else $error("update != ~(captnupdt|shiftnld)");
  end

  // Completeness and mutual exclusion of clock gating
  assert property (@(posedge clk or negedge clk)
                   ((mainclk | updateclk) == clk) && ((mainclk & updateclk) == 1'b0))
    else $error("Clock gating invariant violated");

  // Basic mode coverage (all input combinations with expected outputs)
  cover property (@(posedge clk) (captnupdt==0 && shiftnld==0 && mainclk==1 && updateclk==0 && capture==0 && update==1));
  cover property (@(posedge clk) (captnupdt==0 && shiftnld==1 && mainclk==0 && updateclk==1 && capture==0 && update==0));
  cover property (@(posedge clk) (captnupdt==1 && shiftnld==0 && mainclk==0 && updateclk==1 && capture==1 && update==0));
  cover property (@(posedge clk) (captnupdt==1 && shiftnld==1 && mainclk==0 && updateclk==1 && capture==1 && update==0));

  // Pass-through edge coverage when gated
  cover property (@(posedge clk) g  && $rose(updateclk));
  cover property (@(negedge clk) g  && $fell(updateclk));
  cover property (@(posedge clk) !g && $rose(mainclk));
  cover property (@(negedge clk) !g && $fell(mainclk));

endmodule

// Bind into DUT
bind stratixiv_bias_logic stratixiv_bias_logic_sva sva_inst (
  .clk(clk),
  .shiftnld(shiftnld),
  .captnupdt(captnupdt),
  .mainclk(mainclk),
  .updateclk(updateclk),
  .capture(capture),
  .update(update)
);