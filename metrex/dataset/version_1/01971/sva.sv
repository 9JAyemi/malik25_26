// SVA for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  a, b,
  input  logic        select,
  input  logic [3:0]  out,

  // internal signals from top_module (connected via bind .*)
  input  logic [3:0]  add_out_int,
  input  logic [3:0]  sub_out_int,
  input  logic        reset_ff
);

  default clocking cb @(posedge clk); endclocking

  // Arithmetic correctness (guard against X on inputs)
  ap_add_ok: assert property (!$isunknown({a,b}) |-> add_out_int == (a + b)[3:0]);
  ap_sub_ok: assert property (!$isunknown({a,b}) |-> sub_out_int == (a - b)[3:0]);

  // Mux correctness
  ap_mux_ok: assert property (!$isunknown({select,add_out_int,sub_out_int})
                              |-> out == (select ? add_out_int : sub_out_int));

  // End-to-end correctness (directly from inputs)
  ap_e2e_add: assert property (!$isunknown({select,a,b}) && select
                               |-> out == (a + b)[3:0]);
  ap_e2e_sub: assert property (!$isunknown({select,a,b}) && !select
                               |-> out == (a - b)[3:0]);

  // Stability: if inputs stable cycle-to-cycle, outputs stable
  ap_add_stable: assert property ($stable({a,b}) |-> $stable(add_out_int));
  ap_sub_stable: assert property ($stable({a,b}) |-> $stable(sub_out_int));
  ap_out_stable: assert property ($stable({select,add_out_int,sub_out_int})
                                  |-> $stable(out));

  // Knownness propagation
  ap_known_addsub: assert property (!$isunknown({a,b}) |-> !$isunknown({add_out_int,sub_out_int}));
  ap_known_out:    assert property (!$isunknown({select,add_out_int,sub_out_int}) |-> !$isunknown(out));

  // reset_ff behavior (synchronous)
  ap_rst1: assert property (reset  |=> reset_ff);
  ap_rst0: assert property (!reset |=> !reset_ff);

  // Functional coverage
  cp_sel0:   cover property (!select);
  cp_sel1:   cover property ( select);
  cp_sel_tg: cover property ( select ##1 !select);
  cp_sel_gt: cover property (!select ##1  select);

  // Overflow/borrow scenarios
  cp_add_ovf: cover property (select && ((a + b) > 4'hF));
  cp_sub_bor: cover property (!select && (a < b));

  // Reset activity
  cp_rst_rise: cover property ($rose(reset));
  cp_rst_fall: cover property ($fell(reset));

endmodule

// Bind into the DUT (connects internal signals by name)
bind top_module top_module_sva sva_inst (.*);