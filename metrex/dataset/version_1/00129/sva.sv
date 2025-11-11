// SVA bind for dual_edge_ff_and_or_barrelshifter
module dual_edge_ff_and_or_barrelshifter_sva (
  input clk,
  input d,
  input q,
  input [7:0] in,
  input [7:0] out,
  input select,
  input [7:0] constant,
  input d_reg,
  input [7:0] and_result,
  input [7:0] or_result
);
  default clocking cb @(posedge clk); endclocking

  // Constants/structural
  a_const_fixed:        assert property (constant === 8'hAA);
  a_d_reg_passthru:     assert property (d_reg === d);

  // Combinational datapath correctness
  a_sel1_path:          assert property (select  |-> (and_result === (in & constant) && or_result === in              && out === (in & constant)));
  a_sel0_path:          assert property (!select |-> (and_result === in                  && or_result === (in | constant) && out === (in | constant)));
  a_out_no_x:           assert property (! $isunknown({in,select}) |-> ! $isunknown(out));

  // q behavior (synchronous, no reset)
  a_q_set_on_d1:        assert property (d    |=> (q === 1'b1));
  a_q_hold_on_d0:       assert property (!d   |=> (q === $past(q)));
  a_q_change_implies_d: assert property ($changed(q) |-> $past(d));
  a_q_monotonic_high:   assert property (q |=> q); // once 1, never falls

  // Targeted coverage
  c_sel1_mask_all_ones: cover  property (select  && in == 8'hFF && out == constant);
  c_sel0_or_from_zero:  cover  property (!select && in == 8'h00 && out == constant);
  c_q_change:           cover  property (d ##1 $changed(q));
  c_select_toggle:      cover  property (select ##1 !select ##1 select);
endmodule

bind dual_edge_ff_and_or_barrelshifter dual_edge_ff_and_or_barrelshifter_sva sva (.*);