// SVA for interrupt_controller
// Bindable, concise, coverage + key functional checks

module ic_sva #(parameter int n=4, m=2, p=3)
(
  input  logic [n-1:0] irq,
  input  logic [n-1:0] irq_active,
  input  logic [n-1:0] irq_priority,
  input  logic [p-1:0] highest_priority,
  input  logic [m-1:0] iak_active,
  input  logic [m-1:0] iak
);
  default clocking cb @(posedge $global_clock); endclocking

  // Expected highest priority (min of active irq priorities; p if none)
  function automatic int exp_hp(input logic [n-1:0] act, input logic [n-1:0] pri);
    int hp = p;
    for (int j=0; j<n; j++) if (act[j]) hp = (int'(pri[j]) < hp) ? int'(pri[j]) : hp;
    return hp;
  endfunction

  `define KNOWN !$isunknown({irq, irq_active, irq_priority, highest_priority, iak_active})

  // Basic mapping/invariants
  ap_active_map:       assert property (disable iff(!`KNOWN) (irq_active == irq));
  ap_pri_stable:       assert property (disable iff(!`KNOWN) $stable(irq_priority));
  ap_hp_correct:       assert property (disable iff(!`KNOWN) (int'(highest_priority) == exp_hp(irq_active, irq_priority)));
  ap_iak_map:          assert property (disable iff(!`KNOWN) (int'(highest_priority) < m) |-> (iak_active == (logic [m-1:0]) (1 << int'(highest_priority))));
  ap_iak_zero_oob:     assert property (disable iff(!`KNOWN) (int'(highest_priority) >= m) |-> (iak_active == '0));
  ap_iak_onehot0:      assert property (disable iff(!`KNOWN) $onehot0(iak_active));
  ap_iak_out_assign:   assert property (disable iff(!`KNOWN) (iak == iak_active));
  ap_no_x_o:           assert property (disable iff($isunknown(irq)) !$isunknown(iak));

  // Strong corner checks for this DUT’s 1-bit priority encoding
  ap_hp_zero_if_pri0:  assert property (disable iff(!`KNOWN) (|(irq_active & ~irq_priority)) |-> (int'(highest_priority) == 0));
  ap_hp_one_if_pri1:   assert property (disable iff(!`KNOWN) (~|(irq_active & ~irq_priority) && |(irq_active & irq_priority)) |-> (int'(highest_priority) == 1));

  // Coverage
  cover_none:          cover property (~|irq);
  cover_pri0:          cover property (|(irq & ~irq_priority));
  cover_pri1_only:     cover property (~|(irq & ~irq_priority) && |(irq & irq_priority));
  cover_both:          cover property (|(irq & ~irq_priority) && |(irq & irq_priority));
  genvar k;
  generate for (k=0; k<n; k++) begin : g_cov
    cover property (irq[k]);
  end endgenerate

  `undef KNOWN
endmodule

// Bind into DUT
bind interrupt_controller ic_sva #(.n(n), .m(m), .p(p)) u_ic_sva (
  .irq(irq),
  .irq_active(irq_active),
  .irq_priority(irq_priority),
  .highest_priority(highest_priority),
  .iak_active(iak_active),
  .iak(iak)
);