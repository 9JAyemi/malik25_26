// ============================================================
// pci_master_property.sv — Assertions for pci_master.sv
// ============================================================
module pci_master_property #(
  // Timing knobs (in cycles at posedge clk)
  parameter int unsigned MAX_ADDR_TO_IRDY = 3,   // after FRAME_ falls, IRDY_ must go low within N
  parameter int unsigned MAX_DATA_GAP     = 16   // bound for TRDY_ response / activity
)(
  input  logic        clk,
  input  logic        reset_,   // active-low reset
  input  logic        FRAME_,
  input  logic        IRDY_,
  input  logic        TRDY_,
  input  logic        DEVSEL_,
  input  logic [3:0]  C_BE_,
  input  wire  [31:0] AD,

  // Internal DUT signals (bound hierarchically)
  input  logic        AD_enb
);

  // Default sampling; guard assertions during reset asserted low (!reset_)
  default clocking cb @(posedge clk); endclocking
  `define DISABLE_RST disable iff (!reset_)

  // -----------------------------
  // Helper predicates
  // -----------------------------
  function automatic bit bus_is_known32 (logic [31:0] v);
    return !$isunknown(v);
  endfunction

  // Transaction active when FRAME_ is low (simplified for this canned master)
  function automatic bit txn_active ();
    return (FRAME_ == 1'b0);
  endfunction

  // -----------------------------
  // A0: Post-reset idle levels
  // -----------------------------
  ap_reset_idle: assert property (@cb `DISABLE_RST
    $rose(reset_) |-> (FRAME_ && IRDY_)
  ) else $error("After reset_ deassertion, FRAME_/IRDY_ not high.");

  // -----------------------------
  // A1: Address phase requirements
  //  - On FRAME_ falling edge: master drives AD (AD_enb==1)
  //  - Command on C_BE_ must be Memory Read = 4'b0110
  // -----------------------------
  ap_addr_drive_ad: assert property (@cb `DISABLE_RST
    $fell(FRAME_) |-> AD_enb
  ) else $error("Address phase: AD not driven by master (AD_enb==0) on FRAME_ fall.");

  ap_addr_cmd_memread: assert property (@cb `DISABLE_RST
    $fell(FRAME_) |-> (C_BE_ == 4'b0110)
  ) else $error("Address phase: C_BE_ not Memory Read (0110).");

  // -----------------------------
  // A2: IRDY_ must assert (go low) soon after address phase
  // -----------------------------
  ap_irdy_soon: assert property (@cb `DISABLE_RST
    $fell(FRAME_) |-> ##[1:MAX_ADDR_TO_IRDY] (IRDY_ == 1'b0)
  ) else $error("IRDY_ did not assert low within %0d cycles of FRAME_ falling.", MAX_ADDR_TO_IRDY);

  // -----------------------------
  // A3: During data phases when IRDY_==0, master must release AD
  // -----------------------------
  ap_release_ad_on_data: assert property (@cb `DISABLE_RST
    (txn_active() && (IRDY_ == 1'b0)) |-> !AD_enb
  ) else $error("Data phase: Master still driving AD when IRDY_==0.");

  // -----------------------------
  // A4: Byte enables:
  //  - During data phases (IRDY_==0), all bytes enabled (1111)
  //  - C_BE_ must not be Z
endmodule

// ------------------------------------------------------------
// Bind the checker to pci_master
// (bind connects to internals like AD_enb by name inside the DUT)
// ------------------------------------------------------------
bind pci_master pci_master_property #(
  .MAX_ADDR_TO_IRDY(3),
  .MAX_DATA_GAP(16)
) u_pci_master_property (
  .clk     (clk),
  .reset_  (reset_),
  .FRAME_  (FRAME_),
  .IRDY_   (IRDY_),
  .TRDY_   (TRDY_),
  .DEVSEL_ (DEVSEL_),
  .C_BE_   (C_BE_),
  .AD      (AD),

  .AD_enb  (AD_enb)   // internal signal from pci_master
);