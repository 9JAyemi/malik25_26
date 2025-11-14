// SVA for switch_module
// Bind-as-checker, accesses internal signals
module switch_module_sva;

  // Use DUT’s clock/reset implicitly via bind scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Basic mux behavior
  assert property (ej_0 |-> port0_o == port0_0_r);
  assert property (!ej_0 |-> port0_o == port0_local_0);
  assert property (ej_1 |-> port1_o == port1_0_r);
  assert property (!ej_1 |-> port1_o == port1_local_0);

  // Valid semantics
  assert property (valid0 == (port0_0_r[4] && !ej_0));
  assert property (valid1 == (port1_0_r[4] && !ej_1));

  // Ack semantics: implications and key corner cases
  assert property (portl0_ack |-> (!valid0 && (ej_0 || (port0_local_0[4] && !ej_1))));
  assert property (portl1_ack |-> (!valid1 && (ej_1 || (port1_local_0[4] && !ej_0))));
  assert property (ej_0 |-> portl0_ack);
  assert property (ej_1 |-> portl1_ack);
  assert property (valid0 |-> !portl0_ack);
  assert property (valid1 |-> !portl1_ack);
  assert property ((!ej_0 && !ej_1 && port0_local_0[4] && !port0_0_r[4]) |-> portl0_ack);
  assert property ((!ej_0 && !ej_1 && port1_local_0[4] && !port1_0_r[4]) |-> portl1_ack);
  assert property ((!ej_0 && !ej_1 && !port0_local_0[4]) |-> !portl0_ack);
  assert property ((!ej_0 && !ej_1 && !port1_local_0[4]) |-> !portl1_ack);

  // Reset effect on registered path (not disabled by rst)
  // One cycle after rst high, registered inputs cleared and ej/valid deassert
  assert property (@(posedge clk) rst |=> (port0_0_r == 8'h00 && port1_0_r == 8'h00
                                           && !ej_0 && !ej_1 && !valid0 && !valid1));

  // Coverage: exercise both paths and acks
  cover property (ej_0 && portl0_ack);
  cover property (ej_1 && portl1_ack);
  cover property (!ej_0 && !ej_1 && port0_local_0[4] && !port0_0_r[4] && portl0_ack);
  cover property (!ej_0 && !ej_1 && port1_local_0[4] && !port1_0_r[4] && portl1_ack);
  cover property (portl0_ack && portl1_ack);
  cover property (!ej_0 && port0_o == port0_local_0);
  cover property (!ej_1 && port1_o == port1_local_0);
  cover property (ej_0 && port0_o == port0_0_r);
  cover property (ej_1 && port1_o == port1_0_r);
  cover property (rst ##1 (port0_0_r == 8'h00 && port1_0_r == 8'h00 && !ej_0 && !ej_1));

endmodule

bind switch_module switch_module_sva sva_inst();