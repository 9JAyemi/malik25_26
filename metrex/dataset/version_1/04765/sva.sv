// SVA for mux_2to1: bindable, concise, and covers functionality and internals

module mux_2to1_sva
(
  input logic IN0, IN1, S0, OUT,
  input logic S0_not, IN0_and_not_S0, IN1_and_S0
);
  // Functional correctness and internal decomposition (4-state safe)
  always_comb begin
    assert (OUT === (S0 ? IN1 : IN0))
      else $error("MUX func mismatch: S0=%b IN0=%b IN1=%b OUT=%b", S0, IN0, IN1, OUT);

    assert (S0_not === ~S0) else $error("S0_not mismatch");
    assert (IN0_and_not_S0 === (IN0 & ~S0)) else $error("IN0_and_not_S0 mismatch");
    assert (IN1_and_S0 === (IN1 & S0)) else $error("IN1_and_S0 mismatch");
    assert (OUT === (IN0_and_not_S0 | IN1_and_S0)) else $error("OUT OR mismatch");

    if (S0===1'b0 && !$isunknown(IN0)) assert (OUT===IN0) else
    if (S0===1'b1 && !$isunknown(IN1)) assert (OUT===IN1);
  end

  // No overlap of product terms when S0 is known
  always_comb if (!$isunknown(S0)) assert ((IN0_and_not_S0 & IN1_and_S0) === 1'b0)
    else $error("Product term overlap detected");

  // Functional coverage
  covergroup cg_mux;
    cp_sel: coverpoint S0 { bins b0={0}; bins b1={1}; }
    cp_in0: coverpoint IN0 { bins b0={0}; bins b1={1}; }
    cp_in1: coverpoint IN1 { bins b0={0}; bins b1={1}; }
    cr_inputs: cross cp_sel, cp_in0, cp_in1;
  endgroup
  cg_mux cg = new();
  always @(IN0 or IN1 or S0) cg.sample();

  // Tracking/toggle covers
  cover property (@(posedge IN0 or negedge IN0) S0===1'b0 && !$isunknown(IN0) |-> OUT===IN0);
  cover property (@(posedge IN1 or negedge IN1) S0===1'b1 && !$isunknown(IN1) |-> OUT===IN1);
  cover property (@(posedge S0) !$isunknown({IN0,IN1}) |-> OUT===IN1);
  cover property (@(negedge S0) !$isunknown({IN0,IN1}) |-> OUT===IN0);
endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (
  .IN0(IN0),
  .IN1(IN1),
  .S0(S0),
  .OUT(OUT),
  .S0_not(S0_not),
  .IN0_and_not_S0(IN0_and_not_S0),
  .IN1_and_S0(IN1_and_S0)
);