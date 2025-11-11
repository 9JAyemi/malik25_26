// SVA checker for my_module
module my_module_sva (
  input logic X,
  input logic A1, A2, A3,
  input logic B1, B2,
  input logic VPWR, VGND, VPB, VNB
);

  // Convenience
  function automatic logic pwr_ok();
    return (VPWR && !VGND && VPB && !VNB);
  endfunction

  // 1) Functional equivalence when all drivers are known
  always_comb begin
    if (!$isunknown({A1,A2,A3,B1,B2,VPWR,VGND,VPB,VNB})) begin
      assert ( X == (A1 && A2 && A3 && !B1 && !B2 && VPWR && !VGND && VPB && !VNB) )
        else $error("my_module: X != A1&A2&A3&~B1&~B2&VPWR&~VGND&VPB&~VNB");
    end
  end

  // 2) No spurious high: X==1 implies all required literals (4-state strong check)
  always_comb if (X === 1'b1) begin
    assert (A1===1 && A2===1 && A3===1 &&
            B1===0 && B2===0 &&
            VPWR===1 && VGND===0 && VPB===1 && VNB===0)
      else $error("my_module: X high without all required input/power conditions");
  end

  // 3) Power gating: when rails are known but not valid, X must be 0
  always_comb if (!$isunknown({VPWR,VGND,VPB,VNB}) && !pwr_ok()) begin
    assert (X == 1'b0)
      else $error("my_module: X must be 0 when power rails are not valid");
  end

  // 4) Basic functional coverage (hit all key cases)
  // High case
  always_comb cover ( pwr_ok() &&  A1 &&  A2 &&  A3 && !B1 && !B2 && X );

  // Each single-literal low case (with rails OK and all other literals satisfied)
  always_comb cover ( pwr_ok() && !A1 &&  A2 &&  A3 && !B1 && !B2 && !X );
  always_comb cover ( pwr_ok() &&  A1 && !A2 &&  A3 && !B1 && !B2 && !X );
  always_comb cover ( pwr_ok() &&  A1 &&  A2 && !A3 && !B1 && !B2 && !X );
  always_comb cover ( pwr_ok() &&  A1 &&  A2 &&  A3 &&  B1 && !B2 && !X );
  always_comb cover ( pwr_ok() &&  A1 &&  A2 &&  A3 && !B1 &&  B2 && !X );

  // Rail-driven low cases (each rail invalid individually)
  always_comb cover ( !VPWR && !VGND && VPB && !VNB && !X );
  always_comb cover (  VPWR &&  VGND && VPB && !VNB && !X );
  always_comb cover (  VPWR && !VGND && !VPB && !VNB && !X );
  always_comb cover (  VPWR && !VGND && VPB &&  VNB && !X );

endmodule

// Bind into the DUT
bind my_module my_module_sva sva_i (.*);