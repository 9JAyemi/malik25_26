// Assertions/checker for module Test
// Bind into DUT or instantiate in TB. Concise, high-signal-coverage SVA.

module Test_sva (
  input  logic        clk,
  input  logic        rstn,
  input  logic        clken,
  input  logic [3:0]  in,
  input  logic [3:0]  ff_out,
  input  logic [3:0]  fg_out,
  input  logic [3:0]  fh_out
);

  default clocking cb @(posedge clk); endclocking

  // Simple reference model of in_reg (observable via ports only)
  logic [3:0] exp_in_reg;
  always_ff @(posedge clk) begin
    if (!rstn)          exp_in_reg <= '0;
    else if (clken)     exp_in_reg <= in;
  end

  typedef logic [3:0] u4_t;

  // Reset drives all regs/outs to 0 on the following cycle
  assert property (@(cb) !rstn |=> (exp_in_reg==4'h0 && ff_out==4'h0 && fg_out==4'h0 && fh_out==4'h0));

  // Hold behavior when clken==0
  assert property (@(cb) disable iff (!rstn)
                   !clken |=> ($stable(exp_in_reg) && $stable(ff_out) && $stable(fg_out) && $stable(fh_out)));

  // Functional updates when clken==1 (note: outputs use previous in_reg)
  assert property (@(cb) disable iff (!rstn)
                   clken |=> ( ff_out == u4_t'($past(exp_in_reg)*2)
                            && fg_out == u4_t'($past(exp_in_reg)*3)
                            && fh_out == u4_t'($past(exp_in_reg)*4) ));

  // Outputs only change if prior clken==1 (excluding reset effects)
  assert property (@(cb) disable iff (!rstn)
                   ((ff_out != $past(ff_out)) || (fg_out != $past(fg_out)) || (fh_out != $past(fh_out)))
                   |-> $past(clken));

  // No X/Z on outputs when out of reset
  assert property (@(cb) disable iff (!rstn) !$isunknown({ff_out, fg_out, fh_out}));

  // ------------- Coverage -------------
  // Reset deassertion observed
  cover property (@(cb) !rstn ##1 rstn);

  // Back-to-back enables and holds
  cover property (@(cb) disable iff (!rstn) clken[*2]);
  cover property (@(cb) disable iff (!rstn) !clken[*2]);

  // Exercise key input values on enabled cycles (including overflow cases)
  cover property (@(cb) disable iff (!rstn) clken && in==4'h0);
  cover property (@(cb) disable iff (!rstn) clken && in==4'h1);
  cover property (@(cb) disable iff (!rstn) clken && in==4'h7);
  cover property (@(cb) disable iff (!rstn) clken && in==4'h8);
  cover property (@(cb) disable iff (!rstn) clken && in==4'hF);

endmodule

// Bind example (place in TB or a package included by TB)
bind Test Test_sva i_Test_sva (
  .clk    (clk),
  .rstn   (rstn),
  .clken  (clken),
  .in     (in),
  .ff_out (ff_out),
  .fg_out (fg_out),
  .fh_out (fh_out)
);