// SVA for BFM_APB2APB
// Bind this module to the DUT instance. Focused, concise checks and coverage.

module BFM_APB2APB_SVA
(
  input  logic        PCLK_PM,
  input  logic        PRESETN_PM,
  input  logic        PCLK_SC,

  input  logic [31:0] PADDR_PM,
  input  logic        PWRITE_PM,
  input  logic        PENABLE_PM,
  input  logic [31:0] PWDATA_PM,

  input  logic [31:0] PRDATA_PM,
  input  logic        PREADY_PM,
  input  logic        PSLVERR_PM,

  input  logic [15:0] PSEL_SC,
  input  logic [31:0] PADDR_SC,
  input  logic        PWRITE_SC,
  input  logic        PENABLE_SC,
  input  logic [31:0] PWDATA_SC,

  input  logic [31:0] PRDATA_SC,
  input  logic        PREADY_SC,
  input  logic        PSLVERR_SC,

  // internal DUT regs that we assert/cover against
  input  logic        TRIGGER,
  input  logic        DONE,
  input  logic [31:0] PRDATA_HD,
  input  logic        PSLVERR_HD
);

  // -------- Helpers --------
  function automatic logic [15:0] dec16(input logic [3:0] idx);
    dec16 = 16'b1 << idx;
  endfunction

  // -------- PM domain (PCLK_PM) --------
  // Reset behavior
  assert property (@(posedge PCLK_PM) !PRESETN_PM |-> (!TRIGGER && !PREADY_PM && !PSLVERR_PM && (PRDATA_PM==32'h0)))
    else $error("PM reset values incorrect");

  // TRIGGER is raised only on PENABLE_PM rising edge
  assert property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                   $rose(PENABLE_PM) |=> $rose(TRIGGER))
    else $error("TRIGGER must rise on PENABLE_PM rising edge");

  assert property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                   $rose(TRIGGER) |-> $rose(PENABLE_PM))
    else $error("Spurious TRIGGER rise without PENABLE_PM rising");

  // While active and not DONE, no PREADY_PM
  assert property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                   (TRIGGER && !DONE) |-> !PREADY_PM)
    else $error("PREADY_PM asserted before DONE");

  // PREADY_PM: one-cycle pulse, only when DONE; also data/resp update and TRIGGER low
  assert property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                   PREADY_PM |-> (DONE && !TRIGGER && (PRDATA_PM==PRDATA_HD) && (PSLVERR_PM==PSLVERR_HD)))
    else $error("PREADY_PM pulse conditions violated");

  assert property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                   PREADY_PM |=> !PREADY_PM)
    else $error("PREADY_PM must be a single-cycle pulse");

  // -------- SC domain (PCLK_SC) --------
  // When TRIGGER is low (async reset for SC FSM), bus outputs must be idle
  assert property (@(posedge PCLK_SC) !TRIGGER |-> (!PSEL_SC && !PENABLE_SC))
    else $error("SC side not idle while TRIGGER low");

  // APB protocol on SC side
  // Enable requires Select
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   PENABLE_SC |-> PSEL_SC)
    else $error("PENABLE_SC without PSEL_SC");

  // Setup phase then Access phase (1-cycle setup in this design)
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   $rose(PSEL_SC) |-> !PENABLE_SC)
    else $error("PENABLE_SC high on same cycle as PSEL_SC rise");

  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC && !PENABLE_SC) |=> PENABLE_SC)
    else $error("Access phase did not follow setup phase");

  // Hold select/addr/data/control stable until ready
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC && PENABLE_SC && !PREADY_SC) |=> (PSEL_SC && PENABLE_SC &&
                                                             $stable({PADDR_SC,PWRITE_SC,PWDATA_SC,PSEL_SC})))
    else $error("Signals not held stable while waiting for PREADY_SC");

  // Handshake completion drives DONE and deasserts bus next cycle
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC && PENABLE_SC && PREADY_SC) |-> (DONE && ##1 (!PSEL_SC && !PENABLE_SC)))
    else $error("DONE or deassert after ready violated");

  // Capture return data/resp into HD at handshake
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC && PENABLE_SC && PREADY_SC) |=> (PRDATA_HD==$past(PRDATA_SC) && PSLVERR_HD==$past(PSLVERR_SC)))
    else $error("Return data/resp capture mismatch");

  // Decode: one-hot or zero; if nonzero, matches address[27:24]
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   $onehot0(PSEL_SC))
    else $error("PSEL_SC must be one-hot or zero");

  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC!=16'h0) |-> (PSEL_SC==dec16(PADDR_SC[27:24])))
    else $error("PSEL_SC decode does not match PADDR_SC[27:24]");

  // -------- Cross-domain correlation (minimal, robust) --------
  // When handshake completed on SC, PM must eventually pulse PREADY_PM (within a few PM cycles)
  // Note: loose bound to accommodate clock ratios.
  assert property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                   (PSEL_SC && PENABLE_SC && PREADY_SC) |->
                     ##[1:8] $rose(PREADY_PM))
    else $error("PREADY_PM did not follow SC handshake");

  // -------- Coverage --------
  // Cover read and write transactions (sampled on TRIGGER rise)
  cover property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                  $rose(TRIGGER) && !PWRITE_PM);

  cover property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                  $rose(TRIGGER) &&  PWRITE_PM);

  // Cover waitstates: >=2 cycles between PENABLE_SC and PREADY_SC
  cover property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                  (PSEL_SC && !PENABLE_SC) ##1 (PSEL_SC && PENABLE_SC && !PREADY_SC)
                  ##2 (PSEL_SC && PENABLE_SC && PREADY_SC));

  // Cover error and OK responses
  cover property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                  (PSEL_SC && PENABLE_SC && PREADY_SC &&  PSLVERR_SC));

  cover property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                  (PSEL_SC && PENABLE_SC && PREADY_SC && !PSLVERR_SC));

  // Cover back-to-back transfers (minimal idle gap)
  cover property (@(posedge PCLK_PM) disable iff (!PRESETN_PM)
                  PREADY_PM ##[1:3] $rose(TRIGGER) ##[1:8] PREADY_PM);

  // Cover each target select
  genvar i;
  generate
    for (i=0;i<16;i++) begin : gen_sel_cov
      cover property (@(posedge PCLK_SC) disable iff (!TRIGGER)
                      PSEL_SC[i] ##1 PENABLE_SC ##[1:$] PREADY_SC);
    end
  endgenerate

endmodule

// Bind to DUT (adjust instance name binding as needed)
bind BFM_APB2APB BFM_APB2APB_SVA u_BFM_APB2APB_SVA (
  .PCLK_PM(PCLK_PM),
  .PRESETN_PM(PRESETN_PM),
  .PCLK_SC(PCLK_SC),

  .PADDR_PM(PADDR_PM),
  .PWRITE_PM(PWRITE_PM),
  .PENABLE_PM(PENABLE_PM),
  .PWDATA_PM(PWDATA_PM),

  .PRDATA_PM(PRDATA_PM),
  .PREADY_PM(PREADY_PM),
  .PSLVERR_PM(PSLVERR_PM),

  .PSEL_SC(PSEL_SC),
  .PADDR_SC(PADDR_SC),
  .PWRITE_SC(PWRITE_SC),
  .PENABLE_SC(PENABLE_SC),
  .PWDATA_SC(PWDATA_SC),

  .PRDATA_SC(PRDATA_SC),
  .PREADY_SC(PREADY_SC),
  .PSLVERR_SC(PSLVERR_SC),

  .TRIGGER(TRIGGER),
  .DONE(DONE),
  .PRDATA_HD(PRDATA_HD),
  .PSLVERR_HD(PSLVERR_HD)
);