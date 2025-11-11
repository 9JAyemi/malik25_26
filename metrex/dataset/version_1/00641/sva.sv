// SVA for dff. Bind this to the DUT.
// Focus: cycle-accurate behavior, X-propagation, and basic coverage.

module dff_sva #(parameter int WIDTH=1)
(
  input logic                 clk,
  input logic                 rst,
  input logic [WIDTH-1:0]     inp,
  input logic [WIDTH-1:0]     outp
);
  // Clocking and past-valid
  default clocking cb @(posedge clk); endclocking
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // 1-cycle latency and synchronous reset behavior
  // outp at cycle n equals (rst?0:inp) sampled at cycle n-1
  assert property ( outp == ( ($past(rst) === 1'b1) ? '0 : $past(inp) ) )
    else $error("dff: latency/reset relation violated");

  // X-propagation control:
  // If prior-cycle rst=1, outp must be known-zero;
  // If prior-cycle rst=0 and inp was known, outp must be known.
  assert property ( ($past(rst) === 1'b1) |-> (outp === '0) )
    else $error("dff: outp not zero/known after reset");

  assert property ( ($past(rst) !== 1'b1 && !$isunknown($past(inp))) |-> !$isunknown(outp) )
    else $error("dff: introduced X on outp with known inp");

  // Basic functional coverage
  // Cover a reset cycle that clears the flop
  cover property ( rst ##1 (outp === '0) );

  // Cover data capture: input change reflected one cycle later when not in reset
  cover property ( !rst ##1 $changed(inp) ##1 (outp == $past(inp)) );

endmodule

// Bind to all dff instances, inheriting WIDTH from the DUT
bind dff dff_sva #(.WIDTH(WIDTH)) dff_sva_i (.*);