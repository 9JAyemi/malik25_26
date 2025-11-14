// SVA for inverter
// Bind these to the DUT; concise but complete checks and coverage.

module inverter_sva (
  input  logic [0:0] ip,
  input  logic [0:0] op,
  input  logic       clk,
  input  logic       ce,
  input  logic       clr,
  input  logic [0:0] op_reg  // internal from DUT
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 1) Sequential behavior of op_reg
  // Update on ce
  assert property (disable iff (!past_valid)
                   ce |=> (op_reg == ~ $past(ip)))
    else $error("op_reg did not update to ~ip on ce");

  // Hold when !ce
  assert property (disable iff (!past_valid)
                   !ce |=> (op_reg == $past(op_reg)))
    else $error("op_reg changed without ce");

  // Any change in op_reg must be caused by ce
  assert property (disable iff (!past_valid)
                   $changed(op_reg) |-> $past(ce))
    else $error("op_reg changed without prior ce");

  // 2) Combinational gating to output
  // op must always equal clr ? 1'b0 : op_reg
  assert property (@(op or op_reg or clr)
                   disable iff (!past_valid)
                   op === (clr ? 1'b0 : op_reg))
    else $error("op != (clr ? 0 : op_reg)");

  // 3) Sanity: no X/Z on key controls at sampling time
  assert property (!$isunknown({ip, ce, clr}))
    else $error("X/Z detected on ip/ce/clr at clk edge");

  // 4) Optional: end-to-end when not cleared next cycle
  assert property (disable iff (!past_valid)
                   ce |=> (clr ? (op == 1'b0)
                               : (op == ~ $past(ip))))
    else $error("op not consistent with ip and clr");

  // Coverage
  // ce-driven update with both ip values (clr low next cycle)
  cover property (disable iff (!past_valid)
                  ce && (ip==1'b0) ##1 (!clr && op==1'b1));
  cover property (disable iff (!past_valid)
                  ce && (ip==1'b1) ##1 (!clr && op==1'b0));

  // Hold behavior when ce deasserted
  cover property (disable iff (!past_valid)
                  !ce ##1 (op_reg == $past(op_reg)));

  // clr forcing path and transitions
  cover property (clr && (op==1'b0));
  cover property ($rose(clr));
  cover property ($fell(clr));
endmodule

// Bind into the DUT
bind inverter inverter_sva u_inverter_sva (
  .ip(ip),
  .op(op),
  .clk(clk),
  .ce(ce),
  .clr(clr),
  .op_reg(op_reg)
);