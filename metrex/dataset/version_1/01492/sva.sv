// SVA for interrupt_controller
// Concise, high-value checks and coverage

module interrupt_controller_sva (
  input  logic        CLK,
  input  logic        RST,
  input  logic        INTR,
  input  logic        INTR_LEGACY_CLR,
  input  logic        CONFIG_INTERRUPT_MSIENABLE,
  input  logic        INTR_MSI_RDY,
  input  logic [2:0]  rState,
  input  logic        INTR_DONE,
  input  logic        CFG_INTERRUPT_ASSERT,
  input  logic        INTR_MSI_REQUEST
);

  // Local mirror of state encodings (avoid dependency on `define)
  localparam logic [2:0]
    S_INTRCTLR_IDLE           = 3'd0,
    S_INTRCLTR_WORKING        = 3'd1,
    S_INTRCLTR_COMPLETE       = 3'd2,
    S_INTRCLTR_CLEAR_LEGACY   = 3'd3,
    S_INTRCLTR_CLEARING_LEGACY= 3'd4,
    S_INTRCLTR_DONE           = 3'd5;

  // Reset behavior
  assert property (@(posedge CLK) RST |=> rState == S_INTRCTLR_IDLE);

  // Sanity: known/valid encodings and outputs
  assert property (@(posedge CLK) disable iff (RST) !$isunknown(rState));
  assert property (@(posedge CLK) disable iff (RST)
                   rState inside {S_INTRCTLR_IDLE,S_INTRCLTR_WORKING,S_INTRCLTR_COMPLETE,
                                   S_INTRCLTR_CLEAR_LEGACY,S_INTRCLTR_CLEARING_LEGACY,S_INTRCLTR_DONE});
  assert property (@(posedge CLK) disable iff (RST)
                   !$isunknown({INTR_MSI_REQUEST, CFG_INTERRUPT_ASSERT, INTR_DONE}));

  // INTR_DONE correctness and pulse width
  assert property (@(posedge CLK) disable iff (RST) INTR_DONE == (rState == S_INTRCLTR_DONE));
  assert property (@(posedge CLK) disable iff (RST) INTR_DONE |=> !INTR_DONE);

  // Next-state transition checks
  // IDLE
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCTLR_IDLE && !INTR) |=> rState==S_INTRCTLR_IDLE);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCTLR_IDLE && INTR && INTR_MSI_RDY) |=> rState==S_INTRCLTR_COMPLETE);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCTLR_IDLE && INTR && !INTR_MSI_RDY) |=> rState==S_INTRCLTR_WORKING);

  // WORKING
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_WORKING && !INTR_MSI_RDY) |=> rState==S_INTRCLTR_WORKING);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_WORKING && INTR_MSI_RDY) |=> rState==S_INTRCLTR_COMPLETE);

  // COMPLETE
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_COMPLETE && CONFIG_INTERRUPT_MSIENABLE) |=> rState==S_INTRCLTR_DONE);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_COMPLETE && !CONFIG_INTERRUPT_MSIENABLE) |=> rState==S_INTRCLTR_CLEAR_LEGACY);

  // CLEAR_LEGACY
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEAR_LEGACY && !INTR_LEGACY_CLR) |=> rState==S_INTRCLTR_CLEAR_LEGACY);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEAR_LEGACY && INTR_LEGACY_CLR && INTR_MSI_RDY) |=> rState==S_INTRCLTR_DONE);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEAR_LEGACY && INTR_LEGACY_CLR && !INTR_MSI_RDY) |=> rState==S_INTRCLTR_CLEARING_LEGACY);

  // CLEARING_LEGACY
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEARING_LEGACY && !INTR_MSI_RDY) |=> rState==S_INTRCLTR_CLEARING_LEGACY);
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEARING_LEGACY && INTR_MSI_RDY) |=> rState==S_INTRCLTR_DONE);

  // DONE
  assert property (@(posedge CLK) disable iff (RST) (rState==S_INTRCLTR_DONE) |=> rState==S_INTRCTLR_IDLE);

  // Output correctness per state/inputs
  // IDLE
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCTLR_IDLE && INTR) |-> (INTR_MSI_REQUEST && (CFG_INTERRUPT_ASSERT == !CONFIG_INTERRUPT_MSIENABLE)));
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCTLR_IDLE && !INTR) |-> (!INTR_MSI_REQUEST && !CFG_INTERRUPT_ASSERT));

  // WORKING
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_WORKING) |-> (INTR_MSI_REQUEST && (CFG_INTERRUPT_ASSERT == !CONFIG_INTERRUPT_MSIENABLE)));

  // COMPLETE
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_COMPLETE) |-> (!INTR_MSI_REQUEST && (CFG_INTERRUPT_ASSERT == !CONFIG_INTERRUPT_MSIENABLE)));

  // CLEAR_LEGACY
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEAR_LEGACY && !INTR_LEGACY_CLR) |-> (!INTR_MSI_REQUEST && CFG_INTERRUPT_ASSERT));
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEAR_LEGACY && INTR_LEGACY_CLR) |-> (INTR_MSI_REQUEST && !CFG_INTERRUPT_ASSERT));

  // CLEARING_LEGACY
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_CLEARING_LEGACY) |-> (INTR_MSI_REQUEST && !CFG_INTERRUPT_ASSERT));

  // DONE
  assert property (@(posedge CLK) disable iff (RST)
                   (rState==S_INTRCLTR_DONE) |-> (!INTR_MSI_REQUEST && !CFG_INTERRUPT_ASSERT));

  // Functional coverage
  // MSI path: immediate ready
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCTLR_IDLE && INTR && INTR_MSI_RDY && CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState==S_INTRCLTR_COMPLETE)
    ##1 (rState==S_INTRCLTR_DONE)
    ##1 (rState==S_INTRCTLR_IDLE));

  // MSI path: wait in WORKING then complete
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCTLR_IDLE && INTR && !INTR_MSI_RDY && CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState==S_INTRCLTR_WORKING)[*1:$]
    ##1 (rState==S_INTRCLTR_COMPLETE && INTR_MSI_RDY)
    ##1 (rState==S_INTRCLTR_DONE)
    ##1 (rState==S_INTRCTLR_IDLE));

  // Legacy path: clear immediately leads to DONE
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCTLR_IDLE && INTR && !CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState inside {S_INTRCLTR_WORKING,S_INTRCLTR_COMPLETE})[*1:$]
    ##1 (rState==S_INTRCLTR_COMPLETE && !CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState==S_INTRCLTR_CLEAR_LEGACY && !INTR_LEGACY_CLR && CFG_INTERRUPT_ASSERT)
    ##1 (rState==S_INTRCLTR_CLEAR_LEGACY && INTR_LEGACY_CLR && INTR_MSI_RDY)
    ##1 (rState==S_INTRCLTR_DONE)
    ##1 (rState==S_INTRCTLR_IDLE));

  // Legacy path: clear while not ready -> CLEARING_LEGACY hold then DONE
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCTLR_IDLE && INTR && !CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState inside {S_INTRCLTR_WORKING,S_INTRCLTR_COMPLETE})[*1:$]
    ##1 (rState==S_INTRCLTR_COMPLETE && !CONFIG_INTERRUPT_MSIENABLE)
    ##1 (rState==S_INTRCLTR_CLEAR_LEGACY && !INTR_LEGACY_CLR)
    ##1 (rState==S_INTRCLTR_CLEAR_LEGACY && INTR_LEGACY_CLR && !INTR_MSI_RDY)
    ##1 (rState==S_INTRCLTR_CLEARING_LEGACY)[*1:$]
    ##1 (rState==S_INTRCLTR_DONE && INTR_MSI_RDY)
    ##1 (rState==S_INTRCTLR_IDLE));

  // Hold covers
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCLTR_WORKING && !INTR_MSI_RDY) ##1 (rState==S_INTRCLTR_WORKING));
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCLTR_CLEAR_LEGACY && !INTR_LEGACY_CLR) ##1 (rState==S_INTRCLTR_CLEAR_LEGACY));
  cover property (@(posedge CLK) disable iff (RST)
    (rState==S_INTRCLTR_CLEARING_LEGACY && !INTR_MSI_RDY) ##1 (rState==S_INTRCLTR_CLEARING_LEGACY));

endmodule

// Example bind (place in a separate file or testbench):
// bind interrupt_controller interrupt_controller_sva sva (
//   .CLK(CLK), .RST(RST), .INTR(INTR), .INTR_LEGACY_CLR(INTR_LEGACY_CLR),
//   .CONFIG_INTERRUPT_MSIENABLE(CONFIG_INTERRUPT_MSIENABLE), .INTR_MSI_RDY(INTR_MSI_RDY),
//   .rState(rState), .INTR_DONE(INTR_DONE), .CFG_INTERRUPT_ASSERT(CFG_INTERRUPT_ASSERT),
//   .INTR_MSI_REQUEST(INTR_MSI_REQUEST)
// );