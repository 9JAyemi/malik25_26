// SVA for top_module: 8-stage negedge pipeline
// Bind into DUT; concise checks and coverage

module top_module_sva (input clk, input [7:0] d, output [7:0] q);
  // local cycle counter for safe $past use
  int nedge_cnt;
  always @(negedge clk) nedge_cnt++;

  // Use negedge clocking for pipeline properties
  default clocking cb @ (negedge clk); endclocking

  // 1-cycle shift across entire chain (concise vector form)
  property shift_chain_1cycle;
    (nedge_cnt > 0) |-> {q_reg8,q_reg7,q_reg6,q_reg5,q_reg4,q_reg3,q_reg2,q_reg1}
                    == $past({q_reg7,q_reg6,q_reg5,q_reg4,q_reg3,q_reg2,q_reg1,d});
  endproperty
  assert property (shift_chain_1cycle);

  // Output equals input delayed by 8 negedges
  property out_is_d_delay8;
    (nedge_cnt > 7) |-> (q == $past(d,8));
  endproperty
  assert property (out_is_d_delay8);

  // q must mirror q_reg8 at all times (both edges)
  assert property (@(negedge clk) q == q_reg8);
  assert property (@(posedge clk) q == q_reg8);

  // Registers (and q) are stable between negedges (no unintended posedge updates)
  assert property (@(posedge clk) disable iff (nedge_cnt == 0)
                   $stable({q_reg1,q_reg2,q_reg3,q_reg4,q_reg5,q_reg6,q_reg7,q_reg8,q}));

  // Coverage: a change on d propagates to q 8 cycles later
  cover property ($changed(d) ##8 (q == $past(d,8) && $changed(q)));
endmodule

bind top_module top_module_sva sva_i (.*);