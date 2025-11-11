// SVA checker for div_clk
module div_clk_sva (
  input logic        clk_in,
  input logic        clk_type,
  input logic        reset,
  input logic        clk_out,
  input logic        clock_div2,
  input logic [2:0]  rst_reg
);

  default clocking cb @(posedge clk_in); endclocking

  // rst_reg: async assert to 3'b111, sync deassert to 3'b000, no illegal values, legal change points
  assert property (@(posedge reset) rst_reg == 3'b111);
  assert property (reset |-> (rst_reg == 3'b111));
  assert property ($fell(reset) |-> (rst_reg == 3'b000));
  assert property (!$isunknown(rst_reg) |-> (rst_reg == 3'b000 || rst_reg == 3'b111));
  assert property (@($global_clock) $changed(rst_reg) |-> ($rose(clk_in) || $rose(reset)));

  // clock_div2: clean divide-by-2 toggle and only changes on clk_in posedge
  assert property (!$isunknown(clock_div2) && !$isunknown($past(clock_div2)) |-> (clock_div2 != $past(clock_div2)));
  assert property (@($global_clock) $changed(clock_div2) |-> $rose(clk_in));

  // clk_out reset behavior (async assert via rst_reg[2], held low while asserted)
  assert property (@(posedge rst_reg[2]) clk_out == 1'b0);
  assert property (rst_reg[2] |-> (clk_out == 1'b0));

  // clk_out only changes on legal events
  assert property (@($global_clock) $changed(clk_out) |-> ($rose(clk_in) || $rose(rst_reg[2])));

  // Mode behavior
  // clk_type==1: when stable high for 2+ cycles and not in reset, clk_out must toggle every clk_in edge
  assert property (disable iff (rst_reg[2]) (clk_type && $past(clk_type)) |-> (clk_out != $past(clk_out)));
  // clk_type==0: when stable low for 2+ cycles and not in reset, clk_out is stuck-high (as implemented)
  assert property (disable iff (rst_reg[2]) (!clk_type && $past(!clk_type)) |-> (clk_out && $past(clk_out)));

  // X checks on output when controls are known
  assert property (!$isunknown({clk_type,rst_reg[2]}) |-> !$isunknown(clk_out));

  // Coverage
  cover property (@(posedge reset) 1);
  cover property ($fell(reset));
  cover property (disable iff (rst_reg[2]) (clk_type && $past(clk_type) && (clk_out != $past(clk_out))));
  cover property (disable iff (rst_reg[2]) (!clk_type && $past(!clk_type) && clk_out));
  cover property ($changed(clk_type));

endmodule

// Bind into DUT (accesses internals)
bind div_clk div_clk_sva u_div_clk_sva (.*);