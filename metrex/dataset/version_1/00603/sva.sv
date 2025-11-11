// SVA bind module for synchronizer_ff
module synchronizer_ff_sva #(parameter N=4) ();
  default clocking cb @(posedge s_aclk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge s_aclk) past_valid <= 1'b1;

  // Structural tie-off: Q must mirror Q_reg_reg
  assert property (Q == Q_reg_reg)
    else $error("Q != Q_reg_reg");

  // Cycle-accurate functional spec:
  // Q(t) = rd_rst_reg_reg(t-1) ? D(t-1) : 0
  assert property (past_valid |-> Q == ($past(rd_rst_reg_reg) ? $past(D) : {N{1'b0}}))
    else $error("Functional mismatch: Q not equal to mux(past reset, past D, 0)");

  // Reset must clear within one cycle (redundant with functional spec, but explicit)
  assert property (!rd_rst_reg_reg |=> Q == {N{1'b0}})
    else $error("Reset did not clear Q in 1 cycle");

  // Sanity: reset must be known at sampling edge
  assert property (!$isunknown(rd_rst_reg_reg))
    else $error("rd_rst_reg_reg is X/Z at clock edge");

  // Coverage
  cover property ($fell(rd_rst_reg_reg) ##1 $rose(rd_rst_reg_reg));        // reset pulse observed
  cover property (rd_rst_reg_reg && $changed(D) |=> $changed(Q));          // data transfer observed
  cover property (!rd_rst_reg_reg |=> Q == {N{1'b0}});                     // clear observed
endmodule

bind synchronizer_ff synchronizer_ff_sva #(.N(N)) sva_i();