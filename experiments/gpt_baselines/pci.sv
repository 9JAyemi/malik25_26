`timescale 1ns/1ps
`default_nettype none
// ============================================================
// pci_master.sv (PCI Master DUT)
// Simple behavioral model that drives a canned PCI Read txn.
// NOTE: Not a complete PCI master.
// ============================================================

module pci_master (
    input  bit        clk,
    input  bit        reset_,   // active-low reset (de-assertion is posedge)
    input  logic      TRDY_,
    input  logic      DEVSEL_,
    output logic      FRAME_,
    output logic      IRDY_,
    output logic [3:0] C_BE_,
    inout  wire [31:0] AD
);

  // Simple internal storage for two data phases (expandable)
  logic [31:0] data [0:7];

  // Tri-state drive for AD bus
  bit          AD_enb;
  logic [31:0] AD_reg;
  assign AD = AD_enb ? AD_reg : {32{1'bz}};

  initial begin
    // De-assert control signals
    FRAME_ = 1'b1;
    IRDY_  = 1'b1;

    // Don't drive AD yet
    AD_enb = 1'b0;

    // On de-assertion of active-low reset (i.e., reset_ goes high)
    @(posedge reset_);

    // ----------------------------------------------------------
    // Drive FRAME_, AD and C_BE_ (for a memory read command)
    // ----------------------------------------------------------
    @(negedge clk);
    FRAME_ = 1'b0;

    // check1
    `ifdef check1
      AD_reg = 32'h0000_1234;
    `else
      AD_reg = 32'h0000_1234;
      AD_enb = 1'b1;
    `endif

    // C/BE# = 0110 => Memory Read (command)
    C_BE_ = 4'b0110;
    $display("\n\tDrive FRAME_, AD and Read Command");

    // ----------------------------------------------------------
    // Start the cycle (and drive Byte Enables)
    // ----------------------------------------------------------
    @(negedge clk);
    IRDY_  = 1'b0;
    AD_enb = 1'b0;          // release AD (target will drive on data phases)
    C_BE_  = 4'b1111;       // all byte enables active
    $display("\n\tDrive IRDY_ and Byte Enables");

    // ----------------------------------------------------------
    // Data phase 0: wait for TRDY_ to assert (go low) and sample
    // ----------------------------------------------------------
    @(negedge TRDY_);
    if (!DEVSEL_) data[0] = AD;
    $display("\n\tData Transfer Phase");

    // ----------------------------------------------------------
    // Data phase 1
    // ----------------------------------------------------------
    @(negedge TRDY_);
    if (!DEVSEL_) data[1] = AD;
    $display("\n\tData Transfer Phase");

    // ----------------------------------------------------------
    // Insert a master wait state (deassert IRDY_)
    // ----------------------------------------------------------
    @(negedge clk);
    IRDY_ = 1'b1;
    $display("\n\tMaster Wait Mode");

    // ----------------------------------------------------------
    // Remove wait state
    // ----------------------------------------------------------
    @(negedge clk);
    if (!DEVSEL_ && !TRDY_) data[1] = AD;

    // check3
    `ifdef check3
      IRDY_ = 1'b1;
    `else
      IRDY_ = 1'b0;
    `endif
    $display("\n\tData Transfer Phase");

    // ----------------------------------------------------------
    // De-assert FRAME_ (last data phase already issued)
    // ----------------------------------------------------------
    @(negedge clk);
    FRAME_ = 1'b1;
    $display("\n\tFRAME_ De-asserted");

    // ----------------------------------------------------------
    // De-assert C_BE_ just to introduce bug for check#5
    // ----------------------------------------------------------
    `ifdef check5
      C_BE_ = 4'bzzzz;
    `endif

    // ----------------------------------------------------------
    // De-assert IRDY_ to complete cycle
    // ----------------------------------------------------------
    @(negedge clk);
    IRDY_ = 1'b1;
    $display("\n\tCYCLE COMPLETE");
  end

endmodule

`default_nettype wire
