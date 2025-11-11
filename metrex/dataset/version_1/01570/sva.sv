// SVA checker for dffrl_async_ns
// Concise, high-quality assertions covering async reset, capture/hold, stability, and X/glitch checks.

module dffrl_async_ns_sva #(parameter SIZE=1)
(
  input  logic               clk,
  input  logic               rst_l,
  input  logic               load,
  input  logic [SIZE-1:0]    din,
  input  logic [SIZE-1:0]    q
);

  // Synchronous behavior (sampled at clk), disabled during reset
  // Capture on load
  assert property (@(posedge clk) disable iff (!rst_l)
                   load |-> (q == $past(din)))
    else $error("q failed to capture din on load");

  // Hold when not loading
  assert property (@(posedge clk) disable iff (!rst_l)
                   !load |-> (q == $past(q)))
    else $error("q failed to hold when load=0");

  // Reset dominates even on clk edge
  assert property (@(posedge clk)
                   !rst_l |-> (q == '0))
    else $error("q not 0 on clk edge while in reset");

  // Asynchronous reset behavior (sampled on global clock)
  // While reset is low, q must be 0
  assert property (@($global_clock)
                   !rst_l |-> (q == '0))
    else $error("q not 0 while reset asserted");

  // On reset assertion, q stays 0 for the entire low-reset window
  assert property (@($global_clock)
                   $fell(rst_l) |-> (q == '0') throughout (!rst_l))
    else $error("q not held at 0 throughout reset");

  // After reset deasserts, q stays 0 until the next clk rising edge
  assert property (@($global_clock)
                   $rose(rst_l) |-> (q == '0') until_with $rose(clk))
    else $error("q not 0 until first clk after reset deassert");

  // q may only change on clk rising edge or reset falling edge (glitch-free)
  assert property (@($global_clock)
                   $changed(q) |-> ($rose(clk) || $fell(rst_l)))
    else $error("q changed without clk or reset event");

  // No X on q when out of reset
  assert property (@($global_clock)
                   rst_l |-> !$isunknown(q))
    else $error("q is X/Z when out of reset");

  // Between edges, keep q stable (redundant with change-only check, but explicit)
  assert property (@($global_clock)
                   rst_l && !$rose(clk) && !$fell(rst_l) |-> !$changed(q))
    else $error("q changed between edges");

  // Coverage
  // See a load capture after reset release
  cover property (@($global_clock)
                  $fell(rst_l) ##[1:10] $rose(rst_l) ##[1:10] $rose(clk));

  cover property (@(posedge clk) disable iff (!rst_l)
                  load && (q == $past(din)));

  cover property (@(posedge clk) disable iff (!rst_l)
                  !load && (q == $past(q)));

endmodule

// Bind into the DUT
bind dffrl_async_ns dffrl_async_ns_sva #(.SIZE(SIZE)) dffrl_async_ns_sva_i
(
  .clk  (clk),
  .rst_l(rst_l),
  .load (load),
  .din  (din),
  .q    (q)
);