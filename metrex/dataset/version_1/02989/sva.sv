// SVA for sky130_fd_sc_lp__a21oi (Y = ~ (B1 | (A1 & A2)))
// Bind this module into the DUT and drive clk from your environment.
// Example:
// bind sky130_fd_sc_lp__a21oi sky130_fd_sc_lp__a21oi_sva u_sva (.clk(tb_clk));

module sky130_fd_sc_lp__a21oi_sva (input logic clk);
  default clocking cb @(posedge clk); endclocking

  // Functional equivalence (gate-level to boolean spec)
  a_func: assert property ( !$isunknown({A1,A2,B1,Y}) |-> (Y == ~(B1 | (A1 & A2))) );

  // Internal net checks (composition)
  a_and: assert property ( !$isunknown({A1,A2,and0_out})     |-> (and0_out     == (A1 & A2)) );
  a_nor: assert property ( !$isunknown({B1,and0_out,nor0_out_Y}) |-> (nor0_out_Y == ~(B1 | and0_out)) );
  a_buf: assert property ( !$isunknown({nor0_out_Y,Y})       |-> (Y == nor0_out_Y) );

  // X-propagation safety
  a_no_x: assert property ( !$isunknown({A1,A2,B1}) |-> !$isunknown(Y) );

  // Basic output activity coverage
  c_y_hi:   cover property (Y);
  c_y_lo:   cover property (!Y);
  c_y_rose: cover property ($rose(Y));
  c_y_fell: cover property ($fell(Y));

  // Exhaustive input-state coverage (3 inputs => 8 combinations)
  c_i000: cover property ({A1,A2,B1} == 3'b000);
  c_i001: cover property ({A1,A2,B1} == 3'b001);
  c_i010: cover property ({A1,A2,B1} == 3'b010);
  c_i011: cover property ({A1,A2,B1} == 3'b011);
  c_i100: cover property ({A1,A2,B1} == 3'b100);
  c_i101: cover property ({A1,A2,B1} == 3'b101);
  c_i110: cover property ({A1,A2,B1} == 3'b110);
  c_i111: cover property ({A1,A2,B1} == 3'b111);
endmodule