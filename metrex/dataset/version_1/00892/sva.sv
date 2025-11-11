// SVA for output_module
// Bind-friendly checker module. Connects to internal regs via bind .*.
module output_module_sva (
  input logic        clk,
  input logic        clkx2,
  input logic        jrst_n,
  input logic [35:0] tw,
  input logic        tr_clk,
  input logic [17:0] tr_data,
  input logic        x1,
  input logic        x2,
  input logic        phase
);

  // Reset behavior
  assert property (@(posedge clk)   !jrst_n |-> (x1 == 1'b0));
  assert property (@(posedge clkx2) !jrst_n |-> ({x2,tr_clk,tr_data} == {1'b0,1'b0,18'b0}));

  // No X/Z after reset deasserted
  assert property (@(posedge clk)   jrst_n |-> !$isunknown(x1));
  assert property (@(posedge clkx2) jrst_n |-> !$isunknown({x2,phase,tr_clk,tr_data}));

  // Clock-domain behaviors (guard first cycle after reset with $past(jrst_n))
  // x1 divides-by-2 (toggles every clk)
  assert property (@(posedge clk)
                   jrst_n && $past(jrst_n) |-> x1 == ~$past(x1));

  // clkx2 domain: one-cycle latency relations
  assert property (@(posedge clkx2)
                   jrst_n && $past(jrst_n) |-> x2 == $past(x1));

  assert property (@(posedge clkx2)
                   jrst_n && $past(jrst_n) |-> phase == $past(x1 ^ x2));

  assert property (@(posedge clkx2)
                   jrst_n && $past(jrst_n) |-> tr_clk == ~$past(phase));

  assert property (@(posedge clkx2)
                   jrst_n && $past(jrst_n) |-> tr_data == $past(phase ? tw[17:0] : tw[35:18]));

  // Functional coverage
  cover property (@(posedge clk)   jrst_n && $past(jrst_n) && x1 != $past(x1)); // x1 toggles
  cover property (@(posedge clkx2) jrst_n && $past(jrst_n) && $changed(tr_clk)); // tr_clk toggles
  cover property (@(posedge clkx2) jrst_n && $past(jrst_n) && $past(phase)==1'b0
                                   && tr_data == $past(tw[35:18])); // upper half sent
  cover property (@(posedge clkx2) jrst_n && $past(jrst_n) && $past(phase)==1'b1
                                   && tr_data == $past(tw[17:0]));  // lower half sent
endmodule

// Bind into DUT (tools that support bind with .* can pick up internal regs)
bind output_module output_module_sva u_output_module_sva (.*);