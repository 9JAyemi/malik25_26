// SVA for sync and dff_async_reset
// Concise checks: async reset behavior, clocked sampling semantics, no-X, basic coverage.

`ifndef SYNC_SVA
`define SYNC_SVA

// Checker for the top-level sync wrapper (ports only; no internal nets required)
module sync_sva
(
  input  wire OutputClock,
  input  wire reset_b,
  input  wire InputData,
  input  wire OutputData
);
  default clocking cb @(posedge OutputClock); endclocking

  // Asynchronous reset forces OutputData low immediately on reset assertion
  assert property (@(negedge reset_b) 1 |-> ##0 (OutputData == 1'b0))
    else $error("sync: OutputData not cleared immediately on async reset assertion");

  // While in reset, OutputData must hold 0
  assert property (!reset_b |-> (OutputData == 1'b0))
    else $error("sync: OutputData != 0 while reset_b is low");

  // When reset_b is high on consecutive clock edges, OutputData is the previous InputData
  assert property ((reset_b && $past(reset_b)) |-> (OutputData == $past(InputData)))
    else $error("sync: OutputData does not reflect prior-cycle InputData");

  // No X/Z on key signals at observation points
  assert property (@(posedge OutputClock) !$isunknown(reset_b))
    else $error("sync: reset_b is X/Z at clock edge");
  assert property (@(posedge OutputClock) !$isunknown(InputData))
    else $error("sync: InputData is X/Z at clock edge");
  assert property (@(posedge OutputClock or negedge reset_b) !$isunknown(OutputData))
    else $error("sync: OutputData is X/Z");

  // Coverage
  cover property (@(negedge reset_b) 1);                         // async reset asserted
  cover property (@(posedge OutputClock) $rose(reset_b));        // reset deasserted
  cover property (reset_b && $past(reset_b) && $changed(InputData)
                  ##1 (OutputData == $past(InputData)));         // data change captured
  cover property (reset_b && $past(reset_b) && ($past(InputData)==1'b0)
                  ##1 (OutputData==1'b0));                       // captured 0
  cover property (reset_b && $past(reset_b) && ($past(InputData)==1'b1)
                  ##1 (OutputData==1'b1));                       // captured 1
endmodule


// Generic checker for the async-reset DFF itself
module dff_async_reset_sva
(
  input  wire clk,
  input  wire reset_b,
  input  wire d,
  input  wire q
);
  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately
  assert property (@(negedge reset_b) 1 |-> ##0 (q == 1'b0))
    else $error("dff_async_reset: q not cleared immediately on async reset");

  // Hold 0 while in reset
  assert property (!reset_b |-> (q == 1'b0))
    else $error("dff_async_reset: q != 0 while reset_b low");

  // Normal clocked sampling when reset_b high on consecutive edges
  assert property ((reset_b && $past(reset_b)) |-> (q == $past(d)))
    else $error("dff_async_reset: q != prior-cycle d");

  // No X/Z
  assert property (@(posedge clk or negedge reset_b) !$isunknown(q))
    else $error("dff_async_reset: q is X/Z");
  assert property (@(posedge clk) !$isunknown(reset_b) && !$isunknown(d))
    else $error("dff_async_reset: reset_b or d is X/Z at clk edge");

  // Coverage
  cover property (@(negedge reset_b) 1);
  cover property (@(posedge clk) $rose(reset_b));
  cover property (reset_b && $past(reset_b) && (d!=q)); // capture causes q to change next edge
endmodule


// Bind the checkers to all instances
bind sync             sync_sva            sync_sva_i (.*);
bind dff_async_reset  dff_async_reset_sva dff_sva_i  (.*);

`endif