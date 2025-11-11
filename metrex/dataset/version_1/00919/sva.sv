// SVA for mux4to1
module mux4to1_sva (
  input  logic [3:0] A0,
  input  logic [3:0] A1,
  input  logic [3:0] A2,
  input  logic [3:0] A3,
  input  logic       S0,
  input  logic       S1,
  input  logic       VPWR,
  input  logic       VGND,
  input  logic       Y
);

  wire        pwr_ok = (VPWR === 1'b1) && (VGND === 1'b0);
  wire [1:0]  sel    = {S1,S0};

  // Core mux correctness (sample after NBA using ##0)
  property p_mux_correct;
    @(A0 or A1 or A2 or A3 or S0 or S1 or VPWR or VGND)
      pwr_ok && !$isunknown(sel) |-> ##0
        (Y === (sel==2'b00 ? A0[0] :
                sel==2'b01 ? A1[0] :
                sel==2'b10 ? A2[0] : A3[0]));
  endproperty
  assert property (p_mux_correct);

  // Hold behavior when select is X/Z (no branch taken -> Y stable)
  property p_hold_on_x_sel;
    @(A0 or A1 or A2 or A3 or S0 or S1)
      pwr_ok && $isunknown(sel) |-> ##0 $stable(Y);
  endproperty
  assert property (p_hold_on_x_sel);

  // Y changes only if select changes or the selected data bit changes
  property p_y_changes_have_cause;
    @(Y)
      pwr_ok |-> ($changed(sel) ||
                  (sel==2'b00 && $changed(A0[0])) ||
                  (sel==2'b01 && $changed(A1[0])) ||
                  (sel==2'b10 && $changed(A2[0])) ||
                  (sel==2'b11 && $changed(A3[0])));
  endproperty
  assert property (p_y_changes_have_cause);

  // Coverage: each select case exercised and correct
  cover property (@(A0 or S0 or S1) pwr_ok && sel==2'b00 ##0 (Y === A0[0]));
  cover property (@(A1 or S0 or S1) pwr_ok && sel==2'b01 ##0 (Y === A1[0]));
  cover property (@(A2 or S0 or S1) pwr_ok && sel==2'b10 ##0 (Y === A2[0]));
  cover property (@(A3 or S0 or S1) pwr_ok && sel==2'b11 ##0 (Y === A3[0]));

  // Coverage: Y follows selected input toggle
  cover property (@(A0[0]) pwr_ok && sel==2'b00 && $changed(A0[0]) ##0 $changed(Y) && (Y===A0[0]));
  cover property (@(A1[0]) pwr_ok && sel==2'b01 && $changed(A1[0]) ##0 $changed(Y) && (Y===A1[0]));
  cover property (@(A2[0]) pwr_ok && sel==2'b10 && $changed(A2[0]) ##0 $changed(Y) && (Y===A2[0]));
  cover property (@(A3[0]) pwr_ok && sel==2'b11 && $changed(A3[0]) ##0 $changed(Y) && (Y===A3[0]));

endmodule

bind mux4to1 mux4to1_sva sva_mux4to1 (
  .A0(A0), .A1(A1), .A2(A2), .A3(A3),
  .S0(S0), .S1(S1),
  .VPWR(VPWR), .VGND(VGND),
  .Y(Y)
);