// SVA for XOR_M
// Bind this module to XOR_M and connect a sampling clock (and optional active-low reset)
module XOR_M_sva (input logic clk, rst_n,
                  input logic Sgn_X, Sgn_Y, Sgn_Info);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on any port
  a_known: assert property (!$isunknown({Sgn_X, Sgn_Y, Sgn_Info}));

  // Functional equivalence
  a_func:  assert property (Sgn_Info == (Sgn_X ^ Sgn_Y));

  // Stability: if inputs don’t change, output doesn’t change
  a_hold:  assert property ($stable(Sgn_X) && $stable(Sgn_Y) |-> $stable(Sgn_Info));

  // Toggle relationships across a cycle
  a_one_toggle_out_toggles:
           assert property (($changed(Sgn_X) ^ $changed(Sgn_Y)) |-> $changed(Sgn_Info));
  a_both_toggle_out_stable:
           assert property ($changed(Sgn_X) && $changed(Sgn_Y) |-> !$changed(Sgn_Info));

  // Truth-table coverage (also implicitly checks correct output per case)
  c_tt00:  cover property (Sgn_X==0 && Sgn_Y==0 && Sgn_Info==0);
  c_tt01:  cover property (Sgn_X==0 && Sgn_Y==1 && Sgn_Info==1);
  c_tt10:  cover property (Sgn_X==1 && Sgn_Y==0 && Sgn_Info==1);
  c_tt11:  cover property (Sgn_X==1 && Sgn_Y==1 && Sgn_Info==0);

  // Transition coverage
  c_x_tog: cover property ($changed(Sgn_X));
  c_y_tog: cover property ($changed(Sgn_Y));
  c_both:  cover property ($changed(Sgn_X) && $changed(Sgn_Y));

endmodule

// Example bind (connect clk/rst_n from your environment):
// bind XOR_M XOR_M_sva u_xor_m_sva(.clk(tb_clk), .rst_n(tb_rst_n),
//                                  .Sgn_X(Sgn_X), .Sgn_Y(Sgn_Y), .Sgn_Info(Sgn_Info));