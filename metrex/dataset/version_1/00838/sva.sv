// SVA for my_module
module my_module_sva (
  input  logic i_0r0, i_0r1, o_0a, reset,
  input  logic o_0r0, o_0r1, i_0a,
  input  logic bna_0, bcomp_0, tech1_oint, tech2_oint
);

  // Pure combinational relations
  assert property (bna_0  == !o_0a);
  assert property (o_0r0  == (i_0r0 & bna_0));
  assert property (o_0r1  == (i_0r1 & bna_0));
  assert property (bcomp_0 == (o_0r0 | o_0r1));
  assert property (i_0a   == bcomp_0);

  // NAND-with-reset internals
  assert property (tech1_oint == ~(o_0r0 & reset));
  assert property (tech2_oint == ~(o_0r1 & reset));

  // Handshake/gating implications
  assert property (o_0a |-> (!o_0r0 && !o_0r1 && !i_0a));
  assert property ((o_0r0 || o_0r1) |-> (!o_0a && i_0a));

  // X-propagation hygiene
  assert property ((!$isunknown({i_0r0,i_0r1,o_0a})) |-> !$isunknown({o_0r0,o_0r1,i_0a}));

  // Functional coverage
  cover property (!o_0a &&  i_0r0 && !i_0r1 &&  o_0r0 && !o_0r1 && i_0a);
  cover property (!o_0a && !i_0r0 &&  i_0r1 && !o_0r0 &&  o_0r1 && i_0a);
  cover property (!o_0a &&  i_0r0 &&  i_0r1 &&  o_0r0 &&  o_0r1 && i_0a);
  cover property ( o_0a && (i_0r0 || i_0r1) && !o_0r0 && !o_0r1 && !i_0a);

  // Reset/NAND coverage
  cover property (reset && o_0r0 && !tech1_oint);
  cover property (reset && o_0r1 && !tech2_oint);
  cover property (!reset && tech1_oint);
  cover property (!reset && tech2_oint);

endmodule

bind my_module my_module_sva u_my_module_sva (
  .i_0r0(i_0r0), .i_0r1(i_0r1), .o_0a(o_0a), .reset(reset),
  .o_0r0(o_0r0), .o_0r1(o_0r1), .i_0a(i_0a),
  .bna_0(bna_0), .bcomp_0(bcomp_0), .tech1_oint(tech1_oint), .tech2_oint(tech2_oint)
);