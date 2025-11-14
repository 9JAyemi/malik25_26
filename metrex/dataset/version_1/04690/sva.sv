// SVA for my_module
// Bind in your testbench: bind my_module my_module_sva sva_inst(.*);

module my_module_sva (
  input logic        clk,
  input logic        rst,
  input logic [2:0]  a, b, c, d,
  input logic [1:0]  e,
  input logic        y,
  // internal state taps
  input logic [2:0]  a_msb, b_msb, c_lsb, d_lsb,
  input logic [1:0]  e_lsb,
  input logic        e_msb
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers that mirror DUT behavior (note: width-mismatch in RTL is intentional here)
  let cond_ab = ($past(a[2:0]) == $past(b[2:0]));
  let cond_cd = ($past(c[2:0]) == $past(d[2:0]));
  let cond_ea = ($past(e[1:0]) == a[2]);
  let cond_ec = ($past(e[0])   == c[0]);
  let cond_y  = (cond_ab && cond_cd && cond_ea && cond_ec);

  // Reset behavior
  // y synchronously clears when rst=1 at a clock edge
  a_reset_y: assert property (rst |=> (y == 1'b0));

  // Internal sampling (only check when previous cycle was active)
  a_pipe_a:  assert property ($past(!rst) |-> (a_msb == $past(a[2:0])));
  a_pipe_b:  assert property ($past(!rst) |-> (b_msb == $past(b[2:0])));
  a_pipe_c:  assert property ($past(!rst) |-> (c_lsb == $past(c[2:0])));
  a_pipe_d:  assert property ($past(!rst) |-> (d_lsb == $past(d[2:0])));
  a_pipe_el: assert property ($past(!rst) |-> (e_lsb == $past(e[1:0])));
  a_pipe_em: assert property ($past(!rst) |-> (e_msb == $past(e[0])));

  // Registers hold steady during reset
  a_regs_hold_on_rst: assert property (rst |=> ($stable(a_msb) && $stable(b_msb) &&
                                               $stable(c_lsb) && $stable(d_lsb) &&
                                               $stable(e_lsb) && $stable(e_msb)));

  // Functional correctness of y (exclude first active cycle after reset)
  a_y_func: assert property ($past(!rst) |-> (y == cond_y));

  // y should never be X/Z in active operation (exclude first active cycle)
  a_y_known: assert property (!rst && $past(!rst) |-> !$isunknown(y));

  // Coverage
  // Hit the exact assert condition driving y=1
  c_y_high:  cover property ($past(!rst) && cond_y);

  // Toggle coverage on y
  c_y_rise:  cover property ($past(!rst) && (y==0) ##1 (y==1));
  c_y_fall:  cover property ($past(!rst) && (y==1) ##1 (y==0));

  // Hit each sub-condition that contributes to y
  c_ab_eq:   cover property ($past(!rst) && cond_ab);
  c_cd_eq:   cover property ($past(!rst) && cond_cd);
  c_ea_eq:   cover property ($past(!rst) && cond_ea); // exposes the 2b vs 1b compare path
  c_ec_eq:   cover property ($past(!rst) && cond_ec);

endmodule