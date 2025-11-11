// SVA checker for mux_2_to_1
module mux_2_to_1_sva (
  input logic select,
  input logic data_0,
  input logic data_1,
  input logic out
);

  // Clockless sampling on any relevant edge
  default clocking cb @(
      posedge select or negedge select or
      posedge data_0 or negedge data_0 or
      posedge data_1 or negedge data_1
  ); endclocking

  // Functional equivalence (4-state aware)
  property p_func;
    out === (select ? data_1 : data_0);
  endproperty
  a_func: assert property(p_func)
    else $error("MUX functional mismatch: out != (select ? data_1 : data_0)");

  // If result is determinable, out must not be X/Z
  property p_no_x_when_determined;
    !$isunknown(select) && !$isunknown(select ? data_1 : data_0)
      |-> !$isunknown(out);
  endproperty
  a_no_x_when_determined: assert property(p_no_x_when_determined)
    else $error("out is X/Z while select and selected data are known");

  // Non-selected input must not affect out
  a_ignore_d1_when_sel0: assert property( (select==0 && $changed(data_1)) |-> ##0 !$changed(out) )
    else $error("Non-selected data_1 change affected out while select==0");

  a_ignore_d0_when_sel1: assert property( (select==1 && $changed(data_0)) |-> ##0 !$changed(out) )
    else $error("Non-selected data_0 change affected out while select==1");

  // Coverage: both data paths and select-driven behavior
  c_sel0_drives:     cover property( select==0 && $changed(data_0) ##0 (out==data_0) );
  c_sel1_drives:     cover property( select==1 && $changed(data_1) ##0 (out==data_1) );
  c_sel_toggle_diff: cover property( $changed(select) && (data_0!=data_1) ##0 $changed(out) );
  c_sel_toggle_same: cover property( $changed(select) && (data_0==data_1) ##0 !$changed(out) );

  // Corner coverage: both values through each leg
  c_sel0_out0: cover property( select==0 && data_0==0 && out==0 );
  c_sel0_out1: cover property( select==0 && data_0==1 && out==1 );
  c_sel1_out0: cover property( select==1 && data_1==0 && out==0 );
  c_sel1_out1: cover property( select==1 && data_1==1 && out==1 );

endmodule

// Bind into the DUT
bind mux_2_to_1 mux_2_to_1_sva u_mux_2_to_1_sva (
  .select(select),
  .data_0(data_0),
  .data_1(data_1),
  .out(out)
);