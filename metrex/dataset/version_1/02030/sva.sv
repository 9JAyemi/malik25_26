// SVA for CLK_GATE_MODULE
// Binds a compact but thorough set of assertions and coverage

module clk_gate_module_sva #(
  parameter bit ASSERT_CTRL_CHANGE_WHEN_CLK_LOW = 0  // set to 1 to enforce glitch-free control usage
) (
  input logic CLK, EN, TE,
  input logic ENCLK
);

  function automatic logic exp_enclk(input logic CLK, EN, TE);
    return (EN && !TE) ? CLK : 1'b0;
  endfunction

  // Continuous functional equivalence (tolerates Xs via case equality)
  always_comb begin
    assert (ENCLK === exp_enclk(CLK, EN, TE))
      else $error("ENCLK mismatch: EN=%0b TE=%0b CLK=%0b ENCLK=%0b", EN, TE, CLK, ENCLK);
  end

  // When inputs are known, ENCLK must be known-correct (no X on ENCLK)
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   (!$isunknown({CLK,EN,TE})) |-> (ENCLK == exp_enclk(CLK,EN,TE)));

  // Pass-through when enabled: EN=1, TE=0 => ENCLK follows CLK edges
  assert property (@(posedge CLK) (EN && !TE) |-> ENCLK);
  assert property (@(negedge CLK) (EN && !TE) |-> !ENCLK);

  // Forced-low when disabled (by EN=0 or TE=1), regardless of CLK edges
  assert property (@(posedge CLK or negedge CLK) ((!EN) || TE) |-> (ENCLK == 1'b0));

  // Control-transition checks (combinational response)
  assert property (@(negedge EN) ENCLK == 1'b0);
  assert property (@(posedge TE) ENCLK == 1'b0);
  assert property (@(negedge TE) ENCLK == exp_enclk(CLK,EN,TE));
  assert property (@(posedge EN) ENCLK == exp_enclk(CLK,EN,TE));

  // Optional: enforce glitch-free control changes (only when CLK is low)
  generate if (ASSERT_CTRL_CHANGE_WHEN_CLK_LOW) begin
    assert property (@(posedge EN or negedge EN) !CLK);
    assert property (@(posedge TE or negedge TE) !CLK);
  end endgenerate

  // Coverage: both gating modes and pass-through edges exercised
  cover property (@(posedge CLK) EN && !TE && ENCLK);
  cover property (@(negedge CLK) EN && !TE && !ENCLK);
  cover property (@(posedge CLK) !EN && (ENCLK==0));
  cover property (@(posedge CLK) TE  && (ENCLK==0));
  cover property (@(posedge EN) !TE);
  cover property (@(posedge TE) EN);

endmodule

bind CLK_GATE_MODULE clk_gate_module_sva sva_i (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));