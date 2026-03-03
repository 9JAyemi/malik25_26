// SVA for AND_GATE — concise, high-quality checks and coverage
// Bindable, no DUT/testbench scaffolding beyond the bind itself

module AND_GATE_sva #(parameter string GSR = "ENABLED")
(
  input logic D0, D1, RST, ECLK, SCLK,
  input logic Q
);
  // Parameter sanity
  initial assert (GSR=="ENABLED" || GSR=="DISABLED")
    else $error("AND_GATE_sva: GSR must be \"ENABLED\" or \"DISABLED\"");

  // Effective synchronous reset (active-high if GSR==ENABLED, else active-low)
  wire rst_act = (GSR == "ENABLED") ? RST : ~RST;

  default clocking cb @(posedge SCLK); endclocking

  // Basic sanity (no X on control paths and output at sampling)
  assert property ( !$isunknown({rst_act,ECLK}) );
  assert property ( (!rst_act && ECLK) |-> !$isunknown({D0,D1}) );
  assert property ( !$isunknown(Q) );

  // Reset: next-cycle clear to 0 and hold at 0 while reset remains asserted
  assert property ( rst_act |=> (Q == 1'b0) );

  // Enable update: when enabled and not in reset, load AND of inputs
  assert property ( (!rst_act && ECLK) |=> (Q == (D0 & D1)) );

  // Hold: when not enabled and not in reset, output holds prior value
  assert property ( (!rst_act && !ECLK) |=> (Q == $past(Q)) );

  // Glitch-free output: Q only changes on SCLK rising edges
  assert property (@($global_clock) $changed(Q) |-> $rose(SCLK));

  // Coverage: reset, load-1, load-0, and hold behavior
  cover property ( rst_act ##1 (Q == 1'b0) );
  cover property ( (!rst_act && ECLK && (D0 & D1)) ##1 (Q == 1'b1) );
  cover property ( (!rst_act && ECLK && !(D0 & D1)) ##1 (Q == 1'b0) );
  cover property ( (!rst_act && !ECLK) ##1 $stable(Q) );
endmodule

// Bind to DUT (connects by port names)
bind AND_GATE AND_GATE_sva #(.GSR(GSR)) and_gate_sva_bind (.*);