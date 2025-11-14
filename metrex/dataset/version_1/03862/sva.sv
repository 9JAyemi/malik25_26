// SVA for data_test2
// Bindable, references DUT internal state

module data_test2_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset state
  ap_reset: assert property (rst |=> din_stb==0 && din_activate==0 && din==32'd0
                                   && write_count==0 && dout_activate==0 && dout_stb==0
                                   && read_count==0 && count_error==0 && incorrect_data==0
                                   && detected_value==32'd0 && count_detected==24'd0);

  // din side
  ap_da_onehot0:   assert property ($onehot0(din_activate));

  // Start/selection and init on ready
  ap_din_start:    assert property ($past(din_ready>0 && din_activate==0)
                                    |-> (write_count==0 && din==0
                                         && din_activate==($past(din_ready[0]) ? 2'b01 : 2'b10)));

  // Strobe only while active and room left; data and counter behavior
  ap_din_stb_gate: assert property (din_stb |-> $past(din_activate!=0 && (write_count < din_size)));
  ap_din_data_inc: assert property (din_stb |-> (din==$past(write_count) && write_count==$past(write_count)+1));
  ap_din_stb_act:  assert property (din_stb |-> (din_activate!=0));

  // Done: when no room left, drop strobe and deactivate next cycle
  ap_din_done:     assert property ($past(din_activate!=0 && !(write_count < din_size)) |-> (!din_stb && din_activate==0));

  // dout side
  // Activate on ready; init read_count
  ap_do_start:     assert property ($past(dout_ready && !dout_activate) |-> (read_count==0 && dout_activate));

  // Count error behavior and pulse
  ap_cnt_err_set:  assert property ($past(dout_ready && !dout_activate && (dout_size!=24'h0800))
                                    |-> (count_error && count_detected==$past(dout_size)));
  ap_cnt_err_ok:   assert property ($past(dout_ready && !dout_activate && (dout_size==24'h0800)) |-> !count_error);
  ap_cnt_err_p:    assert property (count_error |=> !count_error);

  // Strobe only while active and before size; counter increments
  ap_do_stb_gate:  assert property (dout_stb |-> $past(dout_activate && (read_count < dout_size)));
  ap_do_stb_act:   assert property (dout_stb |-> dout_activate);
  ap_do_cnt_inc:   assert property (dout_stb |-> (read_count==$past(read_count)+1));

  // Done: when size reached/exceeded, drop strobe and deactivate next cycle
  ap_do_done:      assert property ($past(dout_activate && !(read_count < dout_size)) |-> (!dout_stb && !dout_activate));

  // incorrect_data semantics and pulse
  ap_bad_set:      assert property ($rose(incorrect_data)
                                    |-> (count_detected==$past(read_count[23:0])
                                         && detected_value==$past(dout)
                                         && $past(dout_activate)
                                         && ($past(read_count)==0 ? ($past(dout)!=32'd0)
                                                                  : ($past(dout)!=$past(read_count)-1))));
  ap_bad_ok:       assert property ($past(dout_activate)
                                    && ($past(read_count)==0 ? ($past(dout)==32'd0)
                                                             : ($past(dout)==$past(read_count)-1))
                                    |-> !incorrect_data);
  ap_bad_p:        assert property (incorrect_data |=> !incorrect_data);

  // Minimal functional coverage
  cp_din_ch0:     cover property ($rose(din_activate[0]));
  cp_din_ch1:     cover property ($rose(din_activate[1]));
  cp_din_done:    cover property ($fell(|din_activate));
  cp_do_start_ok: cover property ($past(dout_ready && !dout_activate && dout_size==24'h0800) |-> dout_activate);
  cp_do_zero:     cover property ($past(dout_ready && !dout_activate && dout_size==24'd0) |-> (dout_activate ##1 !dout_activate));
  cp_cnt_err:     cover property ($rose(count_error));
  cp_bad:         cover property ($rose(incorrect_data));
endmodule

bind data_test2 data_test2_sva sva_i();