// SVA for module: timer
// Bind style: module uses a typed port to access internals.
// Usage example (tool-dependent):
//   bind timer timer_sva #(.TIMEOUT(TIMEOUT)) u_timer_sva (dut);
// or inline these assertions inside the DUT with names adjusted.

module timer_sva #(parameter int unsigned TIMEOUT = 100) (timer dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.rst);

  // Combinational pass-throughs
  a_grant_mirror: assert property (dut.up_grant == dut.down_grant);
  a_ack_mirror:   assert property (dut.down_ack  == dut.up_ack);

  // Functional definitions
  a_timeout_def:  assert property (dut.timeout  == (dut.counter == TIMEOUT));
  a_downreq_def:  assert property (dut.down_req == (dut.up_req & ~dut.timeout));

  // Counter next-state and bounds
  a_cnt_inc:      assert property ( (dut.down_grant && !dut.timeout) |=> dut.counter == $past(dut.counter) + 1 );
  a_cnt_reset:    assert property ( !(dut.down_grant && !dut.timeout) |=> dut.counter == '0 );
  a_cnt_bound:    assert property ( dut.counter <= TIMEOUT );

  // Timeout is a one-cycle pulse when TIMEOUT > 0
  genvar _g;
  if (TIMEOUT > 0) begin : G_TO_ONE_PULSE
    a_to_one_pulse: assert property ( dut.timeout |=> !dut.timeout );
  end

  // Coverage
  c_reach_timeout:         cover property ( (dut.down_grant && !dut.timeout)[*TIMEOUT] ##1 dut.timeout );
  c_block_req_on_timeout:  cover property ( dut.up_req && dut.timeout && !dut.down_req );
  c_basic_path:            cover property ( (dut.up_req && !dut.timeout) ##0 dut.down_req ##0 dut.down_grant ##0 dut.up_grant );

endmodule