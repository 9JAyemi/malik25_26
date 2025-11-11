// SVA checker for sky130_fd_sc_ms__dlxtn
module sky130_fd_sc_ms__dlxtn_sva (
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    input GATE_N,
    input Q
);

function automatic bit is_01(input logic a);
  return (a===1'b0) || (a===1'b1);
endfunction

// Aggregate event to sample on any relevant change
event any_change;
always @(D or VPWR or VGND or VPB or VNB or GATE_N or Q) -> any_change;

// Combinational functional equivalence checks (deferred to avoid NBA races)
always @* begin
  #0;
  if (GATE_N===1'b0) begin
    assert ($isunknown(Q)) else $error("Q must be X when GATE_N==0");
  end
  else if (GATE_N===1'b1) begin
    if (VPWR===1'b1 && VGND===1'b0)        assert (Q===D)    else $error("Q!=D when VPWR=1,VGND=0,GATE_N=1");
    else if (VPWR===1'b0 && VGND===1'b0)   assert (Q===VPB)  else $error("Q!=VPB when VPWR=0,VGND=0,GATE_N=1");
    else if (VPWR===1'b1 && VGND===1'b1)   assert (Q===VNB)  else $error("Q!=VNB when VPWR=1,VGND=1,GATE_N=1");
    else if (VPWR===1'b0 && VGND===1'b1)   assert (Q===VGND) else $error("Q!=VGND when VPWR=0,VGND=1,GATE_N=1");
    // If VPWR/VGND are X/Z, DUT retains Q; no assertion in that case.
  end
end

// No-unknown guarantee under fully-known inputs and gate open
always @* begin
  #0;
  if (GATE_N===1'b1 &&
      is_01(VPWR) && is_01(VGND) &&
      is_01(D) && is_01(VPB) && is_01(VNB)) begin
    assert (!$isunknown(Q)) else $error("Q is X with known inputs and GATE_N==1");
  end
end

////////////////////
// Coverage (concise)
////////////////////
cover property (@(any_change) (GATE_N===1'b0)); // X-prop mode exercised

cover property (@(any_change) (GATE_N===1'b1 && VPWR===1'b1 && VGND===1'b0)); // normal mode
cover property (@(any_change) (GATE_N===1'b1 && VPWR===1'b0 && VGND===1'b0)); // body-bias via VPB
cover property (@(any_change) (GATE_N===1'b1 && VPWR===1'b1 && VGND===1'b1)); // body-bias via VNB
cover property (@(any_change) (GATE_N===1'b1 && VPWR===1'b0 && VGND===1'b1)); // clamp to VGND

// Data transparency exercised in normal mode
cover property (@(any_change)
  (GATE_N===1'b1 && VPWR===1'b1 && VGND===1'b0 && $changed(D)));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__dlxtn sky130_fd_sc_ms__dlxtn_sva dlxtn_sva_bind (
  .D(D), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .GATE_N(GATE_N), .Q(Q)
);