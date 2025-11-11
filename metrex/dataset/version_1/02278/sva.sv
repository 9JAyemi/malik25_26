// SVA checker for MISTRAL_FF
// Focused, high-signal-coverage, concise

`ifndef SYNTHESIS
module MISTRAL_FF_sva (
  input logic DATAIN,
  input logic CLK,
  input logic ACLR,
  input logic ENA,
  input logic SCLR,
  input logic SLOAD,
  input logic SDATA,
  input logic Q
);

  // Basic health: Q never X/Z
  assert property (@(posedge CLK or negedge ACLR) !$isunknown(Q))
    else $error("Q is X/Z");

  // Asynchronous clear behavior
  // Immediate drive to 0 on negedge ACLR
  assert property (@(negedge ACLR) ##0 (Q == 1'b0))
    else $error("Q not 0 on async clear assert");

  // While ACLR low, Q must remain 0 at every clock edge
  assert property (@(posedge CLK) (!ACLR) |-> (Q == 1'b0))
    else $error("Q not 0 while ACLR low");

  // Synchronous behavior (disable during async reset)
  // Priority: SCLR over SLOAD over DATAIN, gated by ENA
  assert property (@(posedge CLK) disable iff (!ACLR)
                   (ENA && SCLR) |=> (Q == 1'b0))
    else $error("SCLR did not clear Q");

  assert property (@(posedge CLK) disable iff (!ACLR)
                   (ENA && !SCLR && SLOAD) |=> (Q == $past(SDATA)))
    else $error("SLOAD path incorrect");

  assert property (@(posedge CLK) disable iff (!ACLR)
                   (ENA && !SCLR && !SLOAD) |=> (Q == $past(DATAIN)))
    else $error("DATAIN path incorrect");

  // Hold when ENA deasserted
  assert property (@(posedge CLK) disable iff (!ACLR)
                   (!ENA) |=> (Q == $past(Q)))
    else $error("Q changed while ENA low");

  // If Q changes on a clock edge (not in reset), ENA must have been 1
  assert property (@(posedge CLK) disable iff (!ACLR)
                   (Q != $past(Q)) |-> ENA)
    else $error("Q changed without ENA");

  // Coverage: exercise all control paths and reset
  cover property (@(negedge ACLR) 1);                         // async clear assert
  cover property (@(posedge CLK) $rose(ACLR));                // reset release
  cover property (@(posedge CLK) disable iff (!ACLR) (ENA && SCLR));
  cover property (@(posedge CLK) disable iff (!ACLR) (ENA && !SCLR && SLOAD));
  cover property (@(posedge CLK) disable iff (!ACLR) (ENA && !SCLR && !SLOAD));
  cover property (@(posedge CLK) disable iff (!ACLR) (!ENA));
  cover property (@(posedge CLK) disable iff (!ACLR) (ENA && SCLR && SLOAD)); // priority case

endmodule

bind MISTRAL_FF MISTRAL_FF_sva sva_inst (
  .DATAIN(DATAIN),
  .CLK(CLK),
  .ACLR(ACLR),
  .ENA(ENA),
  .SCLR(SCLR),
  .SLOAD(SLOAD),
  .SDATA(SDATA),
  .Q(Q)
);
`endif