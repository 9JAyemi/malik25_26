// SVA checker for zet_mux8_1
module zet_mux8_1_sva
(
  input  logic [2:0] sel,
  input  logic       in0, in1, in2, in3, in4, in5, in6, in7,
  input  logic       out
);

  // Known select (catch X/Z on sel)
  property p_sel_known;
    @(sel) !$isunknown(sel);
  endproperty
  assert property (p_sel_known);

  // Functional equivalence: out must reflect selected input (allow 4-state match) after zero-delay settle
  property p_functional_mux;
    @(sel or in0 or in1 or in2 or in3 or in4 or in5 or in6 or in7)
      disable iff ($isunknown(sel))
      1'b1 |-> ##0 (out === ((sel==3'd0)?in0:
                              (sel==3'd1)?in1:
                              (sel==3'd2)?in2:
                              (sel==3'd3)?in3:
                              (sel==3'd4)?in4:
                              (sel==3'd5)?in5:
                              (sel==3'd6)?in6: in7));
  endproperty
  assert property (p_functional_mux);

  // If sel is known and the selected input is known, out must be known (no X leakage)
  property p_no_x_out_when_inputs_known;
    @(sel or in0 or in1 or in2 or in3 or in4 or in5 or in6 or in7)
      (! $isunknown(sel) &&
       ! $isunknown(((sel==3'd0)?in0:
                     (sel==3'd1)?in1:
                     (sel==3'd2)?in2:
                     (sel==3'd3)?in3:
                     (sel==3'd4)?in4:
                     (sel==3'd5)?in5:
                     (sel==3'd6)?in6: in7)))
      |-> ##0 ! $isunknown(out);
  endproperty
  assert property (p_no_x_out_when_inputs_known);

  // Functional coverage: each select value observed
  cover property (@(sel) sel==3'd0);
  cover property (@(sel) sel==3'd1);
  cover property (@(sel) sel==3'd2);
  cover property (@(sel) sel==3'd3);
  cover property (@(sel) sel==3'd4);
  cover property (@(sel) sel==3'd5);
  cover property (@(sel) sel==3'd6);
  cover property (@(sel) sel==3'd7);

  // Functional coverage: when selected input toggles, out follows in zero delay
  cover property (@(in0 or sel)) (! $isunknown(sel) && sel==3'd0 && $changed(in0)) ##0 $changed(out);
  cover property (@(in1 or sel)) (! $isunknown(sel) && sel==3'd1 && $changed(in1)) ##0 $changed(out);
  cover property (@(in2 or sel)) (! $isunknown(sel) && sel==3'd2 && $changed(in2)) ##0 $changed(out);
  cover property (@(in3 or sel)) (! $isunknown(sel) && sel==3'd3 && $changed(in3)) ##0 $changed(out);
  cover property (@(in4 or sel)) (! $isunknown(sel) && sel==3'd4 && $changed(in4)) ##0 $changed(out);
  cover property (@(in5 or sel)) (! $isunknown(sel) && sel==3'd5 && $changed(in5)) ##0 $changed(out);
  cover property (@(in6 or sel)) (! $isunknown(sel) && sel==3'd6 && $changed(in6)) ##0 $changed(out);
  cover property (@(in7 or sel)) (! $isunknown(sel) && sel==3'd7 && $changed(in7)) ##0 $changed(out);

endmodule

// Bind into the DUT (no DUT edits required)
bind zet_mux8_1 zet_mux8_1_sva SVA_ZET_MUX8_1 (
  .sel(sel),
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .in4(in4), .in5(in5), .in6(in6), .in7(in7),
  .out(out)
);