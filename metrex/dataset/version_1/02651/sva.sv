// SVA for t_order_a
// Bind into the DUT instance: bind t_order_a t_order_a_sva sva_i(.*);

module t_order_a_sva
(
  input logic               clk,
  input logic [7:0]         a_to_clk_levm3,
  input logic [7:0]         b_to_clk_levm1,
  input logic [7:0]         c_com_levs10,
  input logic [7:0]         d_to_clk_levm2,
  input logic [7:0]         one,
  input logic [7:0]         m_from_clk_lev1_r,
  input logic [7:0]         n_from_clk_lev2,
  input logic [7:0]         o_from_com_levs11,
  input logic [7:0]         o_from_comandclk_levs12,
  input logic [7:0]         a_to_clk_levm1,
  input logic [7:0]         a_to_clk_levm2,
  input logic [7:0]         c_com_levs11,
  input logic [7:0]         n_from_clk_lev3
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational path equalities (sampled on clk)
  assert property (a_to_clk_levm2 == (a_to_clk_levm3 + 8'd0));
  assert property (a_to_clk_levm1 == (a_to_clk_levm2 + d_to_clk_levm2));
  assert property (a_to_clk_levm1 == (a_to_clk_levm3 + d_to_clk_levm2)); // transitive check
  assert property (c_com_levs11 == (c_com_levs10 + one));
  assert property (o_from_com_levs11 == (c_com_levs10 + 8'd1));
  assert property (n_from_clk_lev2 == m_from_clk_lev1_r);
  assert property (n_from_clk_lev3 == n_from_clk_lev2);
  assert property (o_from_comandclk_levs12 == (c_com_levs11 + n_from_clk_lev3));

  // Sequential register update
  assert property (past_valid |-> m_from_clk_lev1_r == $past(a_to_clk_levm1 + b_to_clk_levm1));

  // Combinational stability: when inputs stable, output stable next sample
  assert property ($stable(c_com_levs11) && $stable(n_from_clk_lev3) |-> $stable(o_from_comandclk_levs12));

  // Minimal functional coverage
  cover property (past_valid && m_from_clk_lev1_r != $past(m_from_clk_lev1_r));
  cover property (past_valid && ($past(b_to_clk_levm1) != 8'd0) && (m_from_clk_lev1_r < $past(a_to_clk_levm1))); // unsigned wrap on sum into flop
  cover property ((c_com_levs11 < c_com_levs10)); // unsigned wrap on c + one
  cover property ($changed(n_from_clk_lev3) && $stable(c_com_levs11));
  cover property ($changed(c_com_levs11) && $stable(n_from_clk_lev3));

endmodule