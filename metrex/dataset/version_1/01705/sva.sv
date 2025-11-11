// SVA for IBUFCTRL
module IBUFCTRL_sva (
  input logic I,
  input logic IBUFDISABLE,
  input logic T,
  input logic O
);

  // Functional spec: when inputs are known, O must equal spec
  property p_func;
    (!$isunknown({IBUFDISABLE,T,I})) |->
      (O === (IBUFDISABLE ? (T ? 1'b0 : 1'b1) : I));
  endproperty
  a_func: assert property (p_func);

  // When enabled, only I drives O (T changes must not affect O)
  property p_indep_T_when_en;
    (! $isunknown(IBUFDISABLE) && !IBUFDISABLE &&
     $changed(T) && !$changed({I,IBUFDISABLE})) |-> ##0 !$changed(O);
  endproperty
  a_indep_T_when_en: assert property (p_indep_T_when_en);

  // When enabled, if only I changes, O must change and match I
  property p_track_when_en;
    (! $isunknown(IBUFDISABLE) && !IBUFDISABLE &&
     $changed(I) && !$changed({T,IBUFDISABLE})) |-> ##0 ($changed(O) && (O===I));
  endproperty
  a_track_when_en: assert property (p_track_when_en);

  // When disabled, only T decides O; I changes must not affect O
  property p_indep_I_when_dis;
    (! $isunknown({IBUFDISABLE,T}) && IBUFDISABLE &&
     $changed(I) && !$changed({T,IBUFDISABLE})) |-> ##0 !$changed(O);
  endproperty
  a_indep_I_when_dis: assert property (p_indep_I_when_dis);

  // Coverage: hit all modes and a mode toggle
  c_enable_path:   cover property (!IBUFDISABLE && !$isunknown(IBUFDISABLE) && $changed(I) && $changed(O));
  c_disable_T1:    cover property (IBUFDISABLE && T  && !$isunknown({IBUFDISABLE,T}) && (O===1'b0));
  c_disable_T0:    cover property (IBUFDISABLE && !T && !$isunknown({IBUFDISABLE,T}) && (O===1'b1));
  c_toggle_disable: cover property ($rose(IBUFDISABLE) or $fell(IBUFDISABLE));

endmodule

bind IBUFCTRL IBUFCTRL_sva IBUFCTRL_sva_i (.*);