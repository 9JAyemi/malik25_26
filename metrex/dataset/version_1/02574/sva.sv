// SVA for mux4_lut16
// Focus: functional correctness, X-prop, and coverage of all select paths.
// Purely combinational, so we trigger on any relevant signal change.

module mux4_lut16_sva (
  input logic I0, I1, I2, I3,
  input logic S0, S1,
  input logic O
);

  function automatic logic f_mux(
    input logic I0, I1, I2, I3,
    input logic S0, S1
  );
    f_mux = ((~S1 & ~S0) & I0) |
            ((~S1 &  S0) & I1) |
            (( S1 & ~S0) & I2) |
            (( S1 &  S0) & I3);
  endfunction

  // Functional equivalence when inputs/selects are known
  property p_mux_func;
    @(I0 or I1 or I2 or I3 or S0 or S1)
      !$isunknown({I0,I1,I2,I3,S0,S1}) |-> (O == f_mux(I0,I1,I2,I3,S0,S1));
  endproperty
  assert property (p_mux_func);

  // No X/Z on output when inputs/selects are known
  property p_no_x_out;
    @(I0 or I1 or I2 or I3 or S0 or S1)
      !$isunknown({I0,I1,I2,I3,S0,S1}) |-> !$isunknown(O);
  endproperty
  assert property (p_no_x_out);

  // Selection-specific equivalence (concise, also aids debug)
  property p_sel_00; @(I0 or I1 or I2 or I3 or S0 or S1) (S1==0 && S0==0) |-> (O === I0); endproperty
  property p_sel_01; @(I0 or I1 or I2 or I3 or S0 or S1) (S1==0 && S0==1) |-> (O === I1); endproperty
  property p_sel_10; @(I0 or I1 or I2 or I3 or S0 or S1) (S1==1 && S0==0) |-> (O === I2); endproperty
  property p_sel_11; @(I0 or I1 or I2 or I3 or S0 or S1) (S1==1 && S0==1) |-> (O === I3); endproperty
  assert property (p_sel_00);
  assert property (p_sel_01);
  assert property (p_sel_10);
  assert property (p_sel_11);

  // Coverage: each select path exercised and observable at O
  cover property (@(I0 or S0 or S1 or O) (S1==0 && S0==0 && O===I0));
  cover property (@(I1 or S0 or S1 or O) (S1==0 && S0==1 && O===I1));
  cover property (@(I2 or S0 or S1 or O) (S1==1 && S0==0 && O===I2));
  cover property (@(I3 or S0 or S1 or O) (S1==1 && S0==1 && O===I3));

  // Coverage: when selected, input edge is immediately reflected on O (##0)
  cover property (@(posedge I0 or negedge I0) (S1==0 && S0==0) ##0 (O===I0));
  cover property (@(posedge I1 or negedge I1) (S1==0 && S0==1) ##0 (O===I1));
  cover property (@(posedge I2 or negedge I2) (S1==1 && S0==0) ##0 (O===I2));
  cover property (@(posedge I3 or negedge I3) (S1==1 && S0==1) ##0 (O===I3));

endmodule

bind mux4_lut16 mux4_lut16_sva u_mux4_lut16_sva (.*);