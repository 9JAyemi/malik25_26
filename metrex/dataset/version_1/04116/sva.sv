// SVA for ps2_kbd. Bind into DUT to access internal state.
module ps2_kbd_sva;
  // Bound into ps2_kbd scope; all DUT signals/regs are visible here.

  default clocking cb @(posedge clk); endclocking
  default disable iff (!clrn);

  // Short-hands
  let samp         = sampling;
  let rdn_rise     = (rdn_falling == 2'b01);
  let valid_frame  = samp && (count == 4'd10) && (buffer[0] == 1'b0) && ps2_data && (^buffer[9:1]);
  let invalid_frame= samp && (count == 4'd10) && !((buffer[0] == 1'b0) && ps2_data && (^buffer[9:1]));

  // Reset behavior
  a_reset:        assert property (!clrn |=> (count==0 && w_ptr==0 && r_ptr==0 && overflow==0));

  // Combinational outputs
  a_ready_def:    assert property (ready == (w_ptr != r_ptr));
  a_data_def:     assert property (data  == fifoo[r_ptr]);

  // Count/bit-capture behavior
  a_count_range:  assert property (count <= 4'd10);
  a_cnt_inc:      assert property (samp && (count != 4'd10) |=> count == $past(count) + 1);
  a_cnt_zero:     assert property (samp && (count == 4'd10) |=> count == 0);
  a_buf_cap:      assert property (samp && (count < 4'd10) |=> buffer[$past(count)] == $past(ps2_data));

  // Accept valid frame: push into FIFO, update overflow
  a_push:         assert property (valid_frame |=> (w_ptr == $past(w_ptr)+1)
                                               && (fifoo[$past(w_ptr)] == $past(buffer[8:1]))
                                               && (overflow == ($past(overflow) | ($past(r_ptr) == ($past(w_ptr)+1)))));

  // Drop invalid frame: no write, overflow stable
  a_no_push:      assert property (invalid_frame |=> (w_ptr == $past(w_ptr)) && (overflow == $past(overflow)));

  // Read side: rdn rising when ready increments r_ptr and clears overflow
  a_read_ok:      assert property (rdn_rise && ready |=> (r_ptr == $past(r_ptr)+1) && (overflow == 1'b0));

  // Read when not ready must not change r_ptr
  a_read_block:   assert property (rdn_rise && !ready |=> r_ptr == $past(r_ptr));

  // Overflow changes only on push or read (besides reset)
  a_oflow_only:   assert property (!(valid_frame || (rdn_rise && ready)) |=> overflow == $past(overflow));

  // If FIFO was empty and a valid frame arrives, ready goes high and data matches written byte
  a_empty_to_ready: assert property (($past(w_ptr)==$past(r_ptr)) && valid_frame
                                     |=> ready && (data == $past(buffer[8:1])));

  // Coverage
  c_valid:        cover property (valid_frame);
  c_invalid:      cover property (invalid_frame);
  c_overflow:     cover property (valid_frame && ($past(r_ptr) == ($past(w_ptr)+1)) |=> overflow);
  c_read:         cover property (ready ##1 (rdn_rise && ready));
  c_w_wrap:       cover property ((w_ptr==3'b111) && valid_frame |=> w_ptr==3'b000);
  c_r_wrap:       cover property ((r_ptr==3'b111) && (rdn_rise && ready) |=> r_ptr==3'b000);
  c_last_read_empties: cover property ((ready && (w_ptr == (r_ptr + 3'b1))) && rdn_rise |=> !ready);

endmodule

bind ps2_kbd ps2_kbd_sva ps2_kbd_sva_i();