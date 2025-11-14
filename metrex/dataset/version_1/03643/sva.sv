// SVA for gci_std_display_device_special_memory
// Bind-friendly assertion module (uses ref to internal array)
module gci_std_display_device_special_memory_sva
  #(parameter USEMEMSIZE = 32'h0000_0000,
    parameter PRIORITY   = 32'h0000_0000,
    parameter DEVICECAT  = 32'h0000_0000)
(
  input  logic         iCLOCK,
  input  logic         inRESET,
  input  logic         iSPECIAL_REQ,
  input  logic         iSPECIAL_RW,
  input  logic [7:0]   iSPECIAL_ADDR,
  input  logic [31:0]  iSPECIAL_DATA,
  input  logic [31:0]  oSPECIAL_DATA,
  ref    logic [31:0]  b_mem [0:255]
);

  default clocking cb @(posedge iCLOCK); endclocking
  default disable iff (!inRESET);

  // Basic X checks when active
  a_no_x_ctrl:    assert property (!$isunknown({iSPECIAL_REQ,iSPECIAL_RW,iSPECIAL_ADDR})); 
  a_no_x_read:    assert property (!$isunknown(oSPECIAL_DATA));

  // Read datapath must reflect memory at addressed location
  a_read_reflects_mem: assert property (oSPECIAL_DATA == b_mem[iSPECIAL_ADDR]);

  // Write: targeted cell gets updated by next cycle
  a_write_updates_target: assert property (
    (iSPECIAL_REQ && iSPECIAL_RW) |=> b_mem[$past(iSPECIAL_ADDR)] == $past(iSPECIAL_DATA)
  );

  // Write: non-targeted cells remain stable
  genvar gi;
  generate
    for (gi=0; gi<256; gi=gi+1) begin: GEN_NO_SPURIOUS_CHANGE
      a_no_spurious_change: assert property (
        (iSPECIAL_REQ && iSPECIAL_RW) |=> (gi == $past(iSPECIAL_ADDR)) || $stable(b_mem[gi])
      );
    end
  endgenerate

  // No write request => memory is stable
  generate
    for (genvar gs=0; gs<256; gs=gs+1) begin: GEN_STABLE_WHEN_NO_WRITE
      a_stable_when_no_write: assert property (
        (!iSPECIAL_REQ || !iSPECIAL_RW) |=> $stable(b_mem[gs])
      );
    end
  endgenerate

  // Asynchronous reset contents (checked during reset)
  // While in reset, the array must be held at init values every clock
  a_rst_usememsize: assert property (@(posedge iCLOCK) (!inRESET) |-> (b_mem[8'd0] == USEMEMSIZE));
  a_rst_priority:   assert property (@(posedge iCLOCK) (!inRESET) |-> (b_mem[8'd1] == PRIORITY));
  generate
    for (genvar rz=0; rz<256; rz=rz+1) begin: GEN_RST_ZERO_OTHERS
      if (rz > 1) begin
        a_rst_others_zero: assert property (@(posedge iCLOCK) (!inRESET) |-> (b_mem[rz] == 32'h0));
      end
    end
  endgenerate

  // Simple functional coverage
  c_reset_seen:     cover property (@(posedge iCLOCK) !inRESET ##1 inRESET);
  c_write_any:      cover property (iSPECIAL_REQ && iSPECIAL_RW);
  c_write_addr0:    cover property (iSPECIAL_REQ && iSPECIAL_RW && (iSPECIAL_ADDR==8'h00));
  c_write_addr1:    cover property (iSPECIAL_REQ && iSPECIAL_RW && (iSPECIAL_ADDR==8'h01));
  c_write_addrFF:   cover property (iSPECIAL_REQ && iSPECIAL_RW && (iSPECIAL_ADDR==8'hFF));
  c_wr_then_readbk: cover property (
    (iSPECIAL_REQ && iSPECIAL_RW, $rose(1'b1)) ##1
    (iSPECIAL_ADDR == $past(iSPECIAL_ADDR) && oSPECIAL_DATA == $past(iSPECIAL_DATA))
  );
  c_two_writes_diff_addr: cover property (
    (iSPECIAL_REQ && iSPECIAL_RW) ##1 (iSPECIAL_REQ && iSPECIAL_RW && iSPECIAL_ADDR != $past(iSPECIAL_ADDR))
  );

endmodule

// Bind into DUT
bind gci_std_display_device_special_memory
  gci_std_display_device_special_memory_sva #(
    .USEMEMSIZE(USEMEMSIZE),
    .PRIORITY  (PRIORITY),
    .DEVICECAT (DEVICECAT)
  ) gci_std_display_device_special_memory_sva_i (
    .iCLOCK(iCLOCK),
    .inRESET(inRESET),
    .iSPECIAL_REQ(iSPECIAL_REQ),
    .iSPECIAL_RW(iSPECIAL_RW),
    .iSPECIAL_ADDR(iSPECIAL_ADDR),
    .iSPECIAL_DATA(iSPECIAL_DATA),
    .oSPECIAL_DATA(oSPECIAL_DATA),
    .b_mem(b_mem)
  );