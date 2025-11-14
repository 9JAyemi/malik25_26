// SVA for dly1_17_mod
// Bind-ready, concise, checks key functionality and reset, plus coverage

module dly1_17_mod_sva (
  input logic        clk,
  input logic        rst,
  input logic [16:0] i,
  input logic [16:0] o,
  input logic        done
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives outputs low while asserted
  assert property (@cb rst |-> (o == '0 && done == 1'b0));

  // o is a 1-cycle delayed version of i (post-reset history)
  assert property (@cb disable iff (rst)
                   o == $past(i, 1, rst));

  // Formal definition of done: compares two consecutive prior i samples
  assert property (@cb disable iff (rst)
                   done == ($past(i,1,rst) == $past(i,2,rst)));

  // Equivalent implications using stability of i
  // If i changed between the last two samples, next cycle done must be 0
  assert property (@cb disable iff (rst)
                   !$stable(i) |-> !done);
  // If i was stable for two consecutive cycles, next cycle done must be 1
  assert property (@cb disable iff (rst)
                   $stable(i)[*2] |-> done);

  // Outputs should not be X/Z after reset is deasserted
  assert property (@cb disable iff (rst)
                   !$isunknown({o,done}));

  // Coverage
  cover property (@cb $rose(rst) ##1 !rst);                            // reset deassert
  cover property (@cb disable iff (rst) $changed(i) ##1 o == $past(i,1,rst)); // o follows i
  cover property (@cb disable iff (rst) $stable(i)[*2] ##1 done);      // done goes high
  cover property (@cb disable iff (rst) !done ##1 done ##1 !done);     // done toggles

endmodule

bind dly1_17_mod dly1_17_mod_sva sva_i (.clk(clk), .rst(rst), .i(i), .o(o), .done(done));