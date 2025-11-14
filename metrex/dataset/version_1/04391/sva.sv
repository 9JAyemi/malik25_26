// SVA checker for mux4. Bind this to the DUT.
// Uses a combinational event clock so no external clock/reset is required.

module mux4_sva(
  input logic       enable,
  input logic [1:0] select,
  input logic       in0, in1, in2, in3,
  input logic       out
);

  // Sample on any change of controls, inputs, or output
  `define COMB_EVT (posedge enable or negedge enable or \
                     posedge select[0] or negedge select[0] or \
                     posedge select[1] or negedge select[1] or \
                     posedge in0 or negedge in0 or \
                     posedge in1 or negedge in1 or \
                     posedge in2 or negedge in2 or \
                     posedge in3 or negedge in3 or \
                     posedge out or negedge out)

  // Controls sanity
  a_no_x_on_select_when_enabled:
    assert property (@(`COMB_EVT) enable |-> !$isunknown(select))
      else $error("select has X/Z while enable=1");

  // Functional mapping (enabled, select known)
  a_func_map:
    assert property (@(`COMB_EVT)
      (enable && !$isunknown(select)) |->
      (out === (select==2'b00 ? in0 :
                select==2'b01 ? in1 :
                select==2'b10 ? in2 : in3)))
      else $error("mux functional mismatch");

  // Disabled forces 0 (select known)
  a_disable_forces_zero:
    assert property (@(`COMB_EVT)
      (!enable && !$isunknown(select)) |->
      (out === 1'b0))
      else $error("out not 0 when disabled");

  // If all drivers/controls are known, out must be known
  a_no_x_out_when_all_known:
    assert property (@(`COMB_EVT)
      (!$isunknown({enable,select,in0,in1,in2,in3})) |->
      !$isunknown(out))
      else $error("out is X/Z with all known inputs/controls");

  // Selected input toggle must toggle out (combinational tracking)
  a_sel0_toggle:
    assert property (@(`COMB_EVT)
      (enable && select==2'b00 && $changed(in0)) |-> $changed(out))
      else $error("out did not track in0 toggle");
  a_sel1_toggle:
    assert property (@(`COMB_EVT)
      (enable && select==2'b01 && $changed(in1)) |-> $changed(out))
      else $error("out did not track in1 toggle");
  a_sel2_toggle:
    assert property (@(`COMB_EVT)
      (enable && select==2'b10 && $changed(in2)) |-> $changed(out))
      else $error("out did not track in2 toggle");
  a_sel3_toggle:
    assert property (@(`COMB_EVT)
      (enable && select==2'b11 && $changed(in3)) |-> $changed(out))
      else $error("out did not track in3 toggle");

  // Functional coverage
  c_enable_lo:   cover property (@(`COMB_EVT) !enable);
  c_enable_hi:   cover property (@(`COMB_EVT) enable);
  c_sel0_used:   cover property (@(`COMB_EVT) enable && select==2'b00);
  c_sel1_used:   cover property (@(`COMB_EVT) enable && select==2'b01);
  c_sel2_used:   cover property (@(`COMB_EVT) enable && select==2'b10);
  c_sel3_used:   cover property (@(`COMB_EVT) enable && select==2'b11);
  c_sel0_path:   cover property (@(`COMB_EVT) enable && select==2'b00 && $changed(in0) && $changed(out));
  c_sel1_path:   cover property (@(`COMB_EVT) enable && select==2'b01 && $changed(in1) && $changed(out));
  c_sel2_path:   cover property (@(`COMB_EVT) enable && select==2'b10 && $changed(in2) && $changed(out));
  c_sel3_path:   cover property (@(`COMB_EVT) enable && select==2'b11 && $changed(in3) && $changed(out));

  `undef COMB_EVT
endmodule

// Bind to all instances of mux4 (no extra ports needed)
bind mux4 mux4_sva mux4_sva_i (.enable(enable), .select(select),
                               .in0(in0), .in1(in1), .in2(in2), .in3(in3),
                               .out(out));