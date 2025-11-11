// SVA for sky130_fd_sc_ms__einvp (tri-state inverter with active-high enable via notif1)
module sky130_fd_sc_ms__einvp_sva (
  input wire Z,
  input wire A,
  input wire TE
);
  // Sample on any change of relevant signals
  default clocking cb @(A or TE or Z); endclocking

  // Functional correctness when enabled and inputs are known
  assert property ( (TE===1'b1 && (A===1'b0 || A===1'b1)) |-> (Z === ~A) )
    else $error("EINVP: Z must be ~A when TE=1 and A is known");

  // Tri-state when disabled
  assert property ( (TE===1'b0) |-> (Z === 1'bz) )
    else $error("EINVP: Z must be Z when TE=0");

  // X-propagation: unknown A while enabled must make Z unknown
  assert property ( (TE===1'b1 && $isunknown(A)) |-> $isunknown(Z) )
    else $error("EINVP: X on A must propagate to Z when TE=1");

  // X-propagation: unknown TE makes output unknown (drive vs. Z is ambiguous)
  assert property ( $isunknown(TE) |-> $isunknown(Z) )
    else $error("EINVP: X on TE must make Z unknown");

  // No spurious Z changes without A or TE changing
  assert property ( $changed(Z) |-> ($changed(A) || $changed(TE)) )
    else $error("EINVP: Z changed without A or TE changing");

  // Coverage: both driven states and tri-state observed
  cover property ( TE===1'b1 && A===1'b0 && Z===1'b1 );
  cover property ( TE===1'b1 && A===1'b1 && Z===1'b0 );
  cover property ( TE===1'b0 && Z===1'bz );

  // Coverage: toggle A while enabled causes Z to complement
  cover property ( (TE===1'b1 && A===1'b0 && Z===1'b1) ##1 (TE===1'b1 && A===1'b1 && Z===1'b0) );

  // Coverage: toggle A while disabled keeps Z at Z
  cover property ( (TE===1'b0 && Z===1'bz) ##1 (TE===1'b0 && $changed(A) && Z===1'bz) );

  // Coverage: X propagation scenarios
  cover property ( TE===1'b1 && $isunknown(A) && $isunknown(Z) );
  cover property ( $isunknown(TE) && $isunknown(Z) );
endmodule

bind sky130_fd_sc_ms__einvp sky130_fd_sc_ms__einvp_sva sva_inst (.Z(Z), .A(A), .TE(TE));