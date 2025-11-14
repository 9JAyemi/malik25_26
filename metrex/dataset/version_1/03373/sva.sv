bind acl_stream_to_vector_converter s2v_sva #(.WIDTH(WIDTH)) s2v_sva_i();

module s2v_sva #(parameter WIDTH=32) ();

  // Equivalences for continuous assigns
  a_stall_out_eq:    assert property (@(posedge clock2x) disable iff (!resetn) (stall_out == sr_in_valid));
  a_stall_sr_eq:     assert property (@(posedge clock2x) disable iff (!resetn) (stall_sr  == (valid_a1 && stall_shift)));
  a_stall_last_eq:   assert property (@(posedge clock)   disable iff (!resetn) (stall_last == valid_out_sr));
  a_valid_out_eq:    assert property (@(posedge clock)   disable iff (!resetn) (valid_out == (valid_out_sr || valid_crossing)));
  a_y_mux_sr:        assert property (@(posedge clock)   disable iff (!resetn) (valid_out_sr  |-> (y1 == y1_sr && y2 == y2_sr)));
  a_y_mux_r:         assert property (@(posedge clock)   disable iff (!resetn) (!valid_out_sr |-> (y1 == y1_r  && y2 == y2_r)));

  // Reset values
  a_rst_fast: assert property (@(posedge clock2x) !resetn |-> (!sr_in_valid && !valid_a1 && !valid_a2));
  a_rst_slow: assert property (@(posedge clock)   !resetn |-> (!valid_crossing && !valid_out_sr));

  // Fast toggle domain
  a_sel_toggle: assert property (@(posedge clock2x) disable iff (!resetn) sel == ~$past(sel));

  // SR skid buffer behavior
  a_sr_rise_only_when_stalled:
    assert property (@(posedge clock2x) disable iff (!resetn)
                     $rose(sr_in_valid) |-> ($past(stall_sr) && !$past(sr_in_valid) && $past(valid_in)));
  a_sr_fall_only_when_unstalled:
    assert property (@(posedge clock2x) disable iff (!resetn)
                     $fell(sr_in_valid) |-> (!$past(stall_sr)));
  a_sr_data_stable_when_full:
    assert property (@(posedge clock2x) disable iff (!resetn)
                     sr_in_valid |-> $stable(dataa_sr));

  // Pair builder invariants (clock2x domain)
  a_a1_implies_a2: assert property (@(posedge clock2x) disable iff (!resetn) (valid_a1 |-> valid_a2));
  a_hold_when_full_and_stalled:
    assert property (@(posedge clock2x) disable iff (!resetn)
                     (valid_a1 && valid_a2 && stall_shift) |->
                     ($stable(valid_a1) && $stable(valid_a2) && $stable(in_a1) && $stable(in_a2)));
  a_shift_when_allowed:
    assert property (@(posedge clock2x) disable iff (!resetn)
                     (valid_a1 && valid_a2 && !stall_shift) |=> (!valid_a1));
  a_w_blocks_shift:
    assert property (@(posedge clock2x) disable iff (!resetn) (!w |-> stall_shift));

  // Crossing stage (clock domain)
  a_cross_hold:
    assert property (@(posedge clock) disable iff (!resetn)
                     (valid_crossing && stall_last) |->
                     ($stable(valid_crossing) && $stable(y1_r) && $stable(y2_r)));

  // Output handshake and stability (clock domain)
  a_out_hold_under_stall:
    assert property (@(posedge clock) disable iff (!resetn)
                     (valid_out && stall_in) |->
                     ($stable(valid_out) && $stable(y1) && $stable(y2)));
  a_out_clear_on_ready:
    assert property (@(posedge clock) disable iff (!resetn)
                     (valid_out_sr && !stall_in) |=> (!valid_out_sr));

  // Coverage
  c_form_pair: cover property (@(posedge clock2x) disable iff (!resetn) (valid_a1 && valid_a2));
  c_sr_used:   cover property (@(posedge clock2x) disable iff (!resetn) $rose(sr_in_valid));
  c_out_txn:   cover property (@(posedge clock)   disable iff (!resetn) (valid_out && !stall_in));
  c_cdc_align: cover property (@(posedge clock2x) disable iff (!resetn) (!w ##1 w));

endmodule