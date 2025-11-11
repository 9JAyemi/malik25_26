// SVA for oh_par2ser. Bind this to the RTL.
// Focus: handshake correctness, counter/load/shift behavior, data path, and key coverage.

module oh_par2ser_sva
  #(parameter PW = 64, parameter SW = 1, parameter CW = $clog2(PW/SW))
(
  input clk, input nreset,
  input [PW-1:0] din,
  input [SW-1:0] dout,
  input access_out,
  input load, input shift,
  input [7:0] datasize,
  input lsbfirst, input fill,
  input wait_in, input wait_out,

  // internal DUT signals (connected by bind)
  input [PW-1:0] shiftreg,
  input [CW-1:0] count,
  input start_transfer,
  input busy
);

  // Basic structural/parameter checks (elaboration-time)
  initial begin
    if (PW <= 0 || SW <= 0) $error("PW/SW must be > 0");
    if (PW % SW != 0)       $error("PW must be a multiple of SW");
    if (CW != $clog2(PW/SW)) $error("CW must be $clog2(PW/SW)");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nreset);

  // Combinational definitions must match
  a_start_transfer_def: assert property (start_transfer == (load && !wait_in && !busy));
  a_busy_def:           assert property (busy == (|count));
  a_access_out_def:     assert property (access_out == busy);
  a_wait_out_def:       assert property (wait_out == (wait_in || busy));

  // Reset effect on counter
  a_reset_count_zero:   assert property (!nreset |-> (count == '0));

  // Counter load/decrement/hold behavior (priority: load > dec > hold)
  a_count_load:         assert property (start_transfer |=> count == $past(datasize[CW-1:0]));
  a_count_dec:          assert property (!start_transfer && shift && busy |=> count == $past(count) - 1'b1);
  a_count_hold:         assert property (!(start_transfer || (shift && busy)) |=> count == $past(count));

  // Shift register update behavior (priority: start_transfer > shift)
  a_sr_load:            assert property (start_transfer |=> shiftreg == $past(din));
  a_sr_shift_lsb:       assert property (!start_transfer && shift && lsbfirst
                                         |=> shiftreg == {{(SW){fill}}, $past(shiftreg[PW-1:SW])});
  a_sr_shift_msb:       assert property (!start_transfer && shift && !lsbfirst
                                         |=> shiftreg == {$past(shiftreg[PW-SW-1:0]), {(SW){fill}}});
  a_sr_hold:            assert property (!(start_transfer || shift) |=> shiftreg == $past(shiftreg));

  // Output mux correctness
  a_dout_mux:           assert property (dout == (lsbfirst ? shiftreg[SW-1:0]
                                                           : shiftreg[PW-1:PW-SW]));

  // Useful coverages
  // Full LSB-first transfer (non-zero length) completes after up to 2**CW shifts
  c_full_xfer_lsb: cover property (start_transfer && (datasize[CW-1:0] != '0) && lsbfirst
                                   ##1 (shift && busy)[*1:(1<<CW)] ##1 !busy);

  // Full MSB-first transfer (non-zero length) completes
  c_full_xfer_msb: cover property (start_transfer && (datasize[CW-1:0] != '0) && !lsbfirst
                                   ##1 (shift && busy)[*1:(1<<CW)] ##1 !busy);

  // Start is blocked by wait_in, then proceeds once wait clears
  c_blocked_then_go: cover property (load && wait_in && !busy
                                     ##[1:10] (!wait_in && load && !busy && start_transfer));

  // Zero-length transfer request
  c_zero_len: cover property (start_transfer && (datasize[CW-1:0] == '0) ##1 !busy);

  // Simultaneous start_transfer and shift (load has priority over shift)
  c_start_and_shift: cover property (start_transfer && shift);

endmodule

// Bind into the DUT
bind oh_par2ser oh_par2ser_sva #(.PW(PW), .SW(SW), .CW(CW)) i_oh_par2ser_sva (.*);