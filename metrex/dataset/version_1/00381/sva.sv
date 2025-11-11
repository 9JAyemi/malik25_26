// SVA bind module for sky130_fd_sc_lp__a21oi
// Function: Y = ~(B1 | (A1 & A2))

bind sky130_fd_sc_lp__a21oi sky130_fd_sc_lp__a21oi_sva a21oi_sva();

module sky130_fd_sc_lp__a21oi_sva;

  // Functional correctness on all-known inputs
  always_comb begin
    if (!$isunknown({A1,A2,B1})) begin
      assert (Y === ~(B1 | (A1 & A2)))
        else $error("a21oi func mismatch: Y=%b A1=%b A2=%b B1=%b", Y,A1,A2,B1);
    end
  end

  // Output X only if some input is X/Z
  always_comb begin
    if ($isunknown(Y)) begin
      assert ($isunknown({A1,A2,B1}))
        else $error("a21oi unexpected X on Y with known inputs: A1=%b A2=%b B1=%b", A1,A2,B1);
    end
  end

  // Internal structure checks (when drivers known)
  always_comb begin
    if (!$isunknown({A1,A2})) begin
      assert (and0_out === (A1 & A2))
        else $error("and0_out mismatch: and0_out=%b A1=%b A2=%b", and0_out,A1,A2);
    end
    if (!$isunknown({B1,and0_out})) begin
      assert (nor0_out_Y === ~(B1 | and0_out))
        else $error("nor0_out_Y mismatch: nor0_out_Y=%b B1=%b and0_out=%b", nor0_out_Y,B1,and0_out);
    end
    if (!$isunknown(nor0_out_Y)) begin
      assert (Y === nor0_out_Y)
        else $error("buf mismatch: Y=%b nor0_out_Y=%b", Y,nor0_out_Y);
    end
  end

  // Power/ground sanity (constants in this cell)
  always_comb begin
    assert (VPWR === 1'b1) else $error("VPWR not 1");
    assert (VGND === 1'b0) else $error("VGND not 0");
    assert (VPB  === 1'b1) else $error("VPB not 1");
    assert (VNB  === 1'b0) else $error("VNB not 0");
  end

  // Truth-table coverage (all input combinations with expected Y)
  always_comb begin
    unique case ({A1,A2,B1})
      3'b000: cover (Y===1);
      3'b001: cover (Y===0);
      3'b010: cover (Y===1);
      3'b011: cover (Y===0);
      3'b100: cover (Y===1);
      3'b101: cover (Y===0);
      3'b110: cover (Y===0);
      3'b111: cover (Y===0);
      default: /* some X/Z present */ ;
    endcase
  end

  // Simple toggle coverage
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);
  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);

endmodule