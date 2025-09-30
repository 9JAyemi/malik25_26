`timescale 1ns/1ps
`default_nettype none
// ============================================================
// LAB6 : pci_protocol_property.sv  (Answers converted to SVA)
// Checks for a canned PCI Read transaction driven by pci_master.sv
// ============================================================

module pci_protocol_property (
  input  logic        clk,
  input  logic        reset_,     // active-low reset
  input  logic        FRAME_,
  input  logic        IRDY_,
  input  logic        TRDY_,
  input  logic        DEVSEL_,
  input  logic [3:0]  C_BE_,
  input  wire  [31:0] AD
);

  // Sample on posedge; disable assertions while reset is asserted low
  default clocking cb @(posedge clk); endclocking
  `define DISABLE_RST disable iff (!reset_)

  // ------------------------------------------------------------
  // CHECK #1.
  // On falling edge of FRAME_, AD or C_BE_ cannot be unknown.
  // ------------------------------------------------------------
`ifdef check1
  property checkPCI_AD_CBE;
    @(cb) `DISABLE_RST
      $fell(FRAME_) |-> ( !$isunknown(AD) && !$isunknown(C_BE_) );
  endproperty
  assert property (checkPCI_AD_CBE)
    else $display($stime,,,"CHECK1:checkPCI_AD_CBE FAIL\n");
`endif

  // ------------------------------------------------------------
  // CHECK #2.
  // When IRDY_ and TRDY_ are asserted (low) AD or C_BE_ cannot be unknown.
  // ------------------------------------------------------------
`ifdef check2
  property checkPCI_DataPhase;
    @(cb) `DISABLE_RST
      (IRDY_==1'b0 && TRDY_==1'b0) |-> ( !$isunknown(AD) && !$isunknown(C_BE_) );
  endproperty
  assert property (checkPCI_DataPhase)
    else $display($stime,,,"CHECK2:checkPCI_DataPhase FAIL\n");
`endif

  // ------------------------------------------------------------
  // CHECK #3.
  // FRAME_ can go high only if IRDY_ is asserted (low).
  // In other words, master may end the cycle only if IRDY_==0.
  // ------------------------------------------------------------
`ifdef check3
  property checkPCI_Frame_Irdy;
    @(cb) `DISABLE_RST
      $rose(FRAME_) |-> (IRDY_==1'b0);
  endproperty
  assert property (checkPCI_Frame_Irdy)
    else $display($stime,,,"CHECK3:checkPCI_frmIrdy FAIL\n");
`endif

  // ------------------------------------------------------------
  // CHECK #4.
  // TRDY_ can be asserted (low) only if DEVSEL_ is asserted (low).
  // ------------------------------------------------------------
`ifdef check4
  property checkPCI_trdyDevsel;
    @(cb) `DISABLE_RST
      $fell(TRDY_) |-> (DEVSEL_==1'b0);
  endproperty
  assert property (checkPCI_trdyDevsel)
    else $display($stime,,,"CHECK4:checkPCI_trdyDevsel FAIL\n");
`endif

  // ------------------------------------------------------------
  // CHECK #5.
  // Once the cycle starts (at FRAME_ assertion), C_BE_ must not float
  // (be X/Z) until FRAME_ is de-asserted.
  // ------------------------------------------------------------
`ifdef check5
  property checkPCI_CBE_during_trx;
    @(cb) `DISABLE_RST
      $fell(FRAME_) |-> (! $isunknown(C_BE_))[*0:$] ##0 $rose(FRAME_);
  endproperty
  assert property (checkPCI_CBE_during_trx)
    else $display($stime,,,"CHECK5:checkPCI_CBE_during_trx FAIL\n");
`endif

endmodule

// ------------------------------------------------------------
// Optional: bind these checks to pci_master
// ------------------------------------------------------------
// bind pci_master pci_protocol_property u_pci_protocol_property (
//   .clk    (clk),
//   .reset_ (reset_),
//   .FRAME_ (FRAME_),
//   .IRDY_  (IRDY_),
//   .TRDY_  (TRDY_),
