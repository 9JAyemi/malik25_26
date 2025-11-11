// SVA checker for sky130_fd_sc_hs__einvn
// Behavior per RTL: Z = (TE_B) ? ~A : A (conditional inverter)

module sky130_fd_sc_hs__einvn_sva (
  input logic A,
  input logic TE_B,
  input logic Z
);

  // Fire assertions/coverage on any edge of inputs or output
  default clocking cb @(posedge A or negedge A or
                        posedge TE_B or negedge TE_B or
                        posedge Z or negedge Z); endclocking

  // Functional correctness on every relevant event
  property p_func; 1 |-> (Z === (TE_B ? ~A : A)); endproperty
  a_func: assert property (p_func);

  // Output never high-impedance
  a_no_z: assert property (1 |-> (Z !== 1'bz));

  // If inputs are known, output must be known and correct
  a_known_deterministic: assert property (
    !$isunknown({A,TE_B}) |-> (! $isunknown(Z) && (Z === (TE_B ? ~A : A)))
  );

  // Stability: if inputs are stable, output must be stable
  a_stable: assert property ( $stable({A,TE_B}) |-> $stable(Z) );

  // Any Z change must be caused by a change on A or TE_B
  a_z_change_caused: assert property ( $changed(Z) |-> ($changed(A) || $changed(TE_B)) );

  // Directional checks
  a_inv_rise:  assert property ( TE_B && $rose(A) |-> $fell(Z) );
  a_inv_fall:  assert property ( TE_B && $fell(A) |-> $rose(Z) );
  a_pas_rise:  assert property ( !TE_B && $rose(A) |-> $rose(Z) );
  a_pas_fall:  assert property ( !TE_B && $fell(A) |-> $fell(Z) );

  // Coverage: exercise both modes, edges, and all input combos
  c_inv_rise:  cover property ( TE_B && $rose(A) && $fell(Z) );
  c_inv_fall:  cover property ( TE_B && $fell(A) && $rose(Z) );
  c_pas_rise:  cover property ( !TE_B && $rose(A) && $rose(Z) );
  c_pas_fall:  cover property ( !TE_B && $fell(A) && $fell(Z) );

  c_te_01_a0:  cover property ( $rose(TE_B) && (A==0) && (Z==~A) );
  c_te_01_a1:  cover property ( $rose(TE_B) && (A==1) && (Z==~A) );
  c_te_10_a0:  cover property ( $fell(TE_B) && (A==0) && (Z== A) );
  c_te_10_a1:  cover property ( $fell(TE_B) && (A==1) && (Z== A) );

  c_combo_00:  cover property ( (A==0) && (TE_B==0) && (Z==A)   );
  c_combo_01:  cover property ( (A==0) && (TE_B==1) && (Z==~A)  );
  c_combo_10:  cover property ( (A==1) && (TE_B==0) && (Z==A)   );
  c_combo_11:  cover property ( (A==1) && (TE_B==1) && (Z==~A)  );

endmodule

// Bind into the DUT
bind sky130_fd_sc_hs__einvn sky130_fd_sc_hs__einvn_sva u_einvn_sva (.*);