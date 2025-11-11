// SVA for srl8_to_64
// Bind this module to the DUT: bind srl8_to_64 srl8_to_64_sva;

module srl8_to_64_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Flatten regBank for simpler checks
  wire [63:0] rb_flat = {regBank[7],regBank[6],regBank[5],regBank[4],regBank[3],regBank[2],regBank[1],regBank[0]};

  // Basic sanity/knownness
  a_known_outs:  assert property (!$isunknown({ready,result}));
  a_known_state: assert property (!$isunknown({status_int,rb_flat}));

  // Status range/invariant
  a_status_range: assert property (status_int inside {[s1:s9]});

  // Output mapping
  a_ready_map:   assert property (ready == (status_int == s9));
  a_result_s9:   assert property ((status_int == s9) |-> (result == rb_flat));
  a_result_else: assert property ((status_int != s9) |-> (result == 64'h0));

  // Synchronous reset effect (checked across the clock)
  a_reset_state: assert property (@(posedge clk) disable iff (1'b0)
                                  reset |=> (status_int == s1) && (rb_flat == 64'h0) && !ready && (result == 64'h0));

  // Status update on enable
  a_en0_step: assert property ((enable == 0)
                               |=> (status_int == ($past(status_int) == s9 ? s1 : $past(status_int)+1)));
  a_en1_to_s1: assert property ((enable == 1) |=> (status_int == s1));

  // Shift behavior when enable==0
  a_shift_chain: assert property ((enable == 0)
                                  |=> (regBank[0] == $past(dataIn)     ) &&
                                      (regBank[1] == $past(regBank[0]) ) &&
                                      (regBank[2] == $past(regBank[1]) ) &&
                                      (regBank[3] == $past(regBank[2]) ) &&
                                      (regBank[4] == $past(regBank[3]) ) &&
                                      (regBank[5] == $past(regBank[4]) ) &&
                                      (regBank[6] == $past(regBank[5]) ) &&
                                      (regBank[7] == $past(regBank[6]) ));

  // Hold behavior when enable==1 (no shifting)
  a_hold_when_en1: assert property ((enable == 1) |=> ($stable(rb_flat)));

  // Ready is a single-cycle pulse
  a_ready_one_pulse: assert property (ready |=> !ready);

  // Wrap behavior from s9 on shift
  a_wrap_on_s9: assert property (((status_int == s9) && (enable == 0))
                                 |=> (status_int == s1) && !ready && (result == 64'h0));

  // End-to-end frame correctness: 8 shifts from s1 produce ready and correct result
  property p_full_frame;
    (status_int == s1) ##1 (enable == 0)[*8];
  endproperty

  a_full_frame_correct: assert property (p_full_frame
                                         |-> (status_int == s9) && ready &&
                                             (result == { $past(dataIn,8), $past(dataIn,7), $past(dataIn,6), $past(dataIn,5),
                                                          $past(dataIn,4), $past(dataIn,3), $past(dataIn,2), $past(dataIn,1) }));

  // Coverage
  c_full_frame: cover property (p_full_frame ##0 (status_int == s9) && ready);
  c_wrap:       cover property ((status_int == s9) && (enable == 0) ##1 (status_int == s1));
  c_pause_then_frame: cover property ((status_int == s1) ##1 (enable == 0)[*3] ##1 (enable == 1)[*2]
                                      ##1 (status_int == s1) ##1 (enable == 0)[*8] ##1 ready);

endmodule

bind srl8_to_64 srl8_to_64_sva;