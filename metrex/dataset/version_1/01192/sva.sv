// Bind these assertions into the DUT
bind valve_controller valve_controller_sva();

module valve_controller_sva;
  // Assumes binding into valve_controller scope; DUT signals are directly visible
  default clocking @(posedge clk); endclocking

  // Reset behavior
  ap_reset_regs: assert property ((reset || clear) |-> (active==0 && shutoff_int==0));

  // Combinational passthrough and valve behavior
  ap_data_passthrough: assert property (data_o == data_i);
  ap_outputs_when_open: assert property (!shutoff_int |-> (dst_rdy_o==dst_rdy_i && src_rdy_o==src_rdy_i));
  ap_outputs_when_shut: assert property (shutoff_int |-> (dst_rdy_o==1'b1 && src_rdy_o==1'b0));
  ap_no_out_xfer_when_shut: assert property (shutoff_int |-> !(src_rdy_o && dst_rdy_i));
  ap_hs_equiv_open: assert property (!shutoff_int |-> ((src_rdy_i && dst_rdy_o) == (src_rdy_o && dst_rdy_i)));

  // active updates on input handshakes
  ap_active_updates_on_in_hs: assert property (disable iff (reset || clear)
    (src_rdy_i && dst_rdy_o) |=> (active == ~$past(data_i[33])));
  ap_active_holds_without_in_hs: assert property (disable iff (reset || clear)
    !(src_rdy_i && dst_rdy_o) |=> (active == $past(active)));

  // shutoff_int update rules
  ap_shutoff_updates_only_when_inactive_next: assert property (disable iff (reset || clear)
    active_next |=> (shutoff_int == $past(shutoff_int)));
  ap_shutoff_captures_when_inactive_next: assert property (disable iff (reset || clear)
    !active_next |=> (shutoff_int == $past(shutoff)));

  // Sanity: no X on control outputs when not in reset
  ap_no_x_controls: assert property (disable iff (reset || clear)
    !$isunknown({src_rdy_o, dst_rdy_o, active, shutoff_int}));

  // Coverage
  cp_in_hs_activates: cover property (disable iff (reset || clear)
    (src_rdy_i && dst_rdy_o && (data_i[33]==1'b0)) ##1 active);
  cp_in_hs_deactivates: cover property (disable iff (reset || clear)
    (src_rdy_i && dst_rdy_o && (data_i[33]==1'b1)) ##1 !active);
  cp_capture_shutoff_1: cover property (disable iff (reset || clear)
    (!active_next && shutoff) ##1 (shutoff_int && (dst_rdy_o && !src_rdy_o)));
  cp_release_shutoff_0: cover property (disable iff (reset || clear)
    (shutoff_int && !active_next && !shutoff) ##1 !shutoff_int);
  cp_open_pass_through_xfer: cover property (disable iff (reset || clear)
    (!shutoff_int && src_rdy_i && dst_rdy_i && src_rdy_o && dst_rdy_o));
endmodule