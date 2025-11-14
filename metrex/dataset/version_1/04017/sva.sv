// SVA for arbiter2
// Bind this file alongside arbiter2.sv

module arbiter2_sva #(
  parameter MAX_DAT_WIDTH = 32,
  parameter WBS_DAT_WIDTH = 32,
  parameter WBM0_DAT_WIDTH = 32,
  parameter WBM1_DAT_WIDTH = 32
)(
  input clk, reset,

  // Master 0
  input [31:0] WBM0_ADR_O,
  input [WBM0_DAT_WIDTH-1:0] WBM0_DAT_O,
  input [WBM0_DAT_WIDTH-1:0] WBM0_DAT_I,
  input [WBM0_DAT_WIDTH/8-1:0] WBM0_SEL_O,
  input  WBM0_WE_O,
  input  WBM0_ACK_I,
  input  WBM0_ERR_I,
  input  WBM0_RTY_I,
  input [2:0] WBM0_CTI_O,
  input [1:0] WBM0_BTE_O,
  input  WBM0_LOCK_O,
  input  WBM0_CYC_O,
  input  WBM0_STB_O,

  // Master 1
  input [31:0] WBM1_ADR_O,
  input [WBM1_DAT_WIDTH-1:0] WBM1_DAT_O,
  input [WBM1_DAT_WIDTH-1:0] WBM1_DAT_I,
  input [WBM1_DAT_WIDTH/8-1:0] WBM1_SEL_O,
  input  WBM1_WE_O,
  input  WBM1_ACK_I,
  input  WBM1_ERR_I,
  input  WBM1_RTY_I,
  input [2:0] WBM1_CTI_O,
  input [1:0] WBM1_BTE_O,
  input  WBM1_LOCK_O,
  input  WBM1_CYC_O,
  input  WBM1_STB_O,

  // Slave side
  input [31:0] WBS_ADR_I,
  input [WBS_DAT_WIDTH-1:0] WBS_DAT_I,
  input [WBS_DAT_WIDTH-1:0] WBS_DAT_O,
  input [WBS_DAT_WIDTH/8-1:0] WBS_SEL_I,
  input  WBS_WE_I,
  input  WBS_ACK_O,
  input  WBS_ERR_O,
  input  WBS_RTY_O,
  input [2:0] WBS_CTI_I,
  input [1:0] WBS_BTE_I,
  input  WBS_LOCK_I,
  input  WBS_CYC_I,
  input  WBS_STB_I,

  // Internal width-adapt wires
  input [MAX_DAT_WIDTH-1:0] WBM0_DAT_I_INT,
  input [MAX_DAT_WIDTH-1:0] WBM0_DAT_O_INT,
  input [MAX_DAT_WIDTH/8-1:0] WBM0_SEL_O_INT,
  input [MAX_DAT_WIDTH-1:0] WBM1_DAT_I_INT,
  input [MAX_DAT_WIDTH-1:0] WBM1_DAT_O_INT,
  input [MAX_DAT_WIDTH/8-1:0] WBM1_SEL_O_INT,
  input [MAX_DAT_WIDTH-1:0] WBS_DAT_O_INT,
  input [MAX_DAT_WIDTH-1:0] WBS_DAT_I_INT,
  input [MAX_DAT_WIDTH/8-1:0] WBS_SEL_I_INT,

  // Internal state
  input [1:0] selected,
  input       locked
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic state checks
  assert property (selected inside {2'd0,2'd1,2'd2}) else $error("selected out of range");
  assert property (reset |-> (selected==2'd0 && !locked)) else $error("Reset state mismatch");

  // Arbitration: grant and priority
  assert property (selected==2'd0 && WBM0_STB_O |=> selected==2'd1) else $error("M0 grant missing");
  assert property (selected==2'd0 && !WBM0_STB_O && WBM1_STB_O |=> selected==2'd2) else $error("M1 grant missing");
  assert property (selected==2'd0 && WBM0_STB_O && WBM1_STB_O |=> selected==2'd1) else $error("Priority to M0 violated");
  assert property ((selected inside {2'd1,2'd2}) |=> (selected==$past(selected) || selected==2'd0)) else $error("Direct 1<->2 switch not allowed");

  // De-select conditions reflect RTL
  assert property ($past(selected)==2'd1 && selected==2'd0 |->
                   $past((WBS_ACK_O || WBS_ERR_O || locked) &&
                         ((WBM0_CTI_O==3'b000)||(WBM0_CTI_O==3'b111)||locked) &&
                         !WBM0_LOCK_O)) else $error("M0 deselect condition mismatch");
  assert property ($past(selected)==2'd2 && selected==2'd0 |->
                   $past((WBS_ACK_O || WBS_ERR_O || locked) &&
                         ((WBM1_CTI_O==3'b000)||(WBM1_CTI_O==3'b111)||locked) &&
                         !WBM1_LOCK_O)) else $error("M1 deselect condition mismatch");
  assert property ($past(selected inside {2'd1,2'd2}) && selected==2'd0 |-> !locked) else $error("locked not cleared on deselect");

  // Lock behavior
  assert property ($past(selected)==2'd0 && $past(WBM0_STB_O) && selected==2'd1 |-> locked==$past(WBM0_LOCK_O)) else $error("locked capture (M0) mismatch");
  assert property ($past(selected)==2'd0 && $past(WBM1_STB_O) && selected==2'd2 |-> locked==$past(WBM1_LOCK_O)) else $error("locked capture (M1) mismatch");
  assert property (locked |-> selected!=2'd0) else $error("locked high while idle");
  assert property (selected==2'd1 && locked && WBM0_LOCK_O |=> selected==2'd1) else $error("M0 lock not holding selection");
  assert property (selected==2'd2 && locked && WBM1_LOCK_O |=> selected==2'd2) else $error("M1 lock not holding selection");

  // Passthrough/muxing to slave
  assert property (selected==2'd1 |->
    (WBS_ADR_I==WBM0_ADR_O   && WBS_WE_I==WBM0_WE_O   && WBS_STB_I==WBM0_STB_O &&
     WBS_CYC_I==WBM0_CYC_O   && WBS_CTI_I==WBM0_CTI_O && WBS_BTE_I==WBM0_BTE_O &&
     WBS_LOCK_I==WBM0_LOCK_O && WBS_SEL_I_INT==WBM0_SEL_O_INT && WBS_DAT_I_INT==WBM0_DAT_O_INT))
    else $error("M0->WBS mux mismatch");

  assert property (selected==2'd2 |->
    (WBS_ADR_I==WBM1_ADR_O   && WBS_WE_I==WBM1_WE_O   && WBS_STB_I==WBM1_STB_O &&
     WBS_CYC_I==WBM1_CYC_O   && WBS_CTI_I==WBM1_CTI_O && WBS_BTE_I==WBM1_BTE_O &&
     WBS_LOCK_I==WBM1_LOCK_O && WBS_SEL_I_INT==WBM1_SEL_O_INT && WBS_DAT_I_INT==WBM1_DAT_O_INT))
    else $error("M1->WBS mux mismatch");

  assert property (selected==2'd0 |->
    (WBS_ADR_I=='0 && WBS_DAT_I_INT=='0 && WBS_SEL_I_INT=='0 &&
     !WBS_WE_I && (WBS_CTI_I=='0) && (WBS_BTE_I=='0) && !WBS_LOCK_I && !WBS_CYC_I && !WBS_STB_I))
    else $error("WBS not idle when no selection");

  // STB implies CYC (Wishbone well-formedness)
  assert property (WBS_STB_I |-> WBS_CYC_I) else $error("WBS_STB without CYC");
  assert property (WBM0_STB_O |-> WBM0_CYC_O) else $error("M0_STB without CYC");
  assert property (WBM1_STB_O |-> WBM1_CYC_O) else $error("M1_STB without CYC");

  // Demuxing of return channels
  assert property (selected==2'd1 |->
                   (WBM0_ACK_I==WBS_ACK_O && WBM1_ACK_I==0 &&
                    WBM0_ERR_I==WBS_ERR_O && WBM1_ERR_I==0 &&
                    WBM0_RTY_I==WBS_RTY_O && WBM1_RTY_I==0))
    else $error("Return demux (M0) mismatch");

  assert property (selected==2'd2 |->
                   (WBM1_ACK_I==WBS_ACK_O && WBM0_ACK_I==0 &&
                    WBM1_ERR_I==WBS_ERR_O && WBM0_ERR_I==0 &&
                    WBM1_RTY_I==WBS_RTY_O && WBM0_RTY_I==0))
    else $error("Return demux (M1) mismatch");

  assert property (selected==2'd0 |->
                   (WBM0_ACK_I==0 && WBM1_ACK_I==0 &&
                    WBM0_ERR_I==0 && WBM1_ERR_I==0 &&
                    WBM0_RTY_I==0 && WBM1_RTY_I==0))
    else $error("Return signals not idle when no selection");

  // Data return fanout to both masters (INT)
  assert property (WBM0_DAT_I_INT==WBS_DAT_O_INT && WBM1_DAT_I_INT==WBS_DAT_O_INT)
    else $error("WBS_DAT_O_INT not fanned to masters");

  // Width adaptation checks (conditional to parameters)
  generate
    if ((WBS_DAT_WIDTH == 8) && ((WBM0_DAT_WIDTH == 32) || (WBM1_DAT_WIDTH == 32))) begin : g_s_w8_m32
      // Slave downsizing: byte select and replicate outbound write data
      assert property (
        (WBS_ADR_I[1:0]==2'b00 |-> WBS_DAT_I == WBS_DAT_I_INT[31:24] && WBS_SEL_I==WBS_SEL_I_INT[3]) &&
        (WBS_ADR_I[1:0]==2'b01 |-> WBS_DAT_I == WBS_DAT_I_INT[23:16] && WBS_SEL_I==WBS_SEL_I_INT[2]) &&
        (WBS_ADR_I[1:0]==2'b10 |-> WBS_DAT_I == WBS_DAT_I_INT[15:8]  && WBS_SEL_I==WBS_SEL_I_INT[1]) &&
        (WBS_ADR_I[1:0]==2'b11 |-> WBS_DAT_I == WBS_DAT_I_INT[7:0]   && WBS_SEL_I==WBS_SEL_I_INT[0]))
        else $error("WBS 32->8 downsize mapping error");
      assert property (WBS_DAT_O_INT == {4{WBS_DAT_O}})
        else $error("WBS_DAT_O_INT replication error");
    end
  endgenerate

  generate
    if ((WBS_DAT_WIDTH == 32) && (WBM0_DAT_WIDTH == 8)) begin : g_m0_w8_s32
      assert property (
        (WBM0_ADR_O[1:0]==2'b00 |-> WBM0_DAT_I == WBM0_DAT_I_INT[31:24] && WBM0_SEL_O_INT=={WBM0_SEL_O,3'b000}) &&
        (WBM0_ADR_O[1:0]==2'b01 |-> WBM0_DAT_I == WBM0_DAT_I_INT[23:16] && WBM0_SEL_O_INT=={1'b0,WBM0_SEL_O,2'b00}) &&
        (WBM0_ADR_O[1:0]==2'b10 |-> WBM0_DAT_I == WBM0_DAT_I_INT[15:8]  && WBM0_SEL_O_INT=={2'b00,WBM0_SEL_O,1'b0}) &&
        (WBM0_ADR_O[1:0]==2'b11 |-> WBM0_DAT_I == WBM0_DAT_I_INT[7:0]   && WBM0_SEL_O_INT=={3'b000,WBM0_SEL_O}))
        else $error("M0 8->32 upsize mapping error");
      assert property (WBM0_DAT_O_INT == {4{WBM0_DAT_O}})
        else $error("M0_DAT_O_INT replication error");
    end else if ((WBS_DAT_WIDTH == 8) && (MAX_DAT_WIDTH == 32)) begin : g_m0_w8_max32
      assert property (WBM0_DAT_I == WBM0_DAT_I_INT) else $error("M0 pass-through DAT_I mismatch");
      assert property (WBM0_SEL_O_INT == {4{WBM0_SEL_O}}) else $error("M0_SEL_O_INT replication error");
      assert property (WBM0_DAT_O_INT == {4{WBM0_DAT_O}}) else $error("M0_DAT_O_INT replication error");
    end else begin : g_m0_else
      assert property (WBM0_DAT_I == WBM0_DAT_I_INT) else $error("M0 DAT_I passthrough mismatch");
      assert property (WBM0_SEL_O_INT == WBM0_SEL_O) else $error("M0 SEL_O passthrough mismatch");
      assert property (WBM0_DAT_O_INT == WBM0_DAT_O) else $error("M0 DAT_O passthrough mismatch");
    end
  endgenerate

  generate
    if ((WBS_DAT_WIDTH == 32) && (WBM1_DAT_WIDTH == 8)) begin : g_m1_w8_s32
      assert property (
        (WBM1_ADR_O[1:0]==2'b00 |-> WBM1_DAT_I == WBM1_DAT_I_INT[31:24] && WBM1_SEL_O_INT=={WBM1_SEL_O,3'b000}) &&
        (WBM1_ADR_O[1:0]==2'b01 |-> WBM1_DAT_I == WBM1_DAT_I_INT[23:16] && WBM1_SEL_O_INT=={1'b0,WBM1_SEL_O,2'b00}) &&
        (WBM1_ADR_O[1:0]==2'b10 |-> WBM1_DAT_I == WBM1_DAT_I_INT[15:8]  && WBM1_SEL_O_INT=={2'b00,WBM1_SEL_O,1'b0}) &&
        (WBM1_ADR_O[1:0]==2'b11 |-> WBM1_DAT_I == WBM1_DAT_I_INT[7:0]   && WBM1_SEL_O_INT=={3'b000,WBM1_SEL_O}))
        else $error("M1 8->32 upsize mapping error");
      assert property (WBM1_DAT_O_INT == {4{WBM1_DAT_O}})
        else $error("M1_DAT_O_INT replication error");
    end else if ((WBS_DAT_WIDTH == 8) && (MAX_DAT_WIDTH == 32)) begin : g_m1_w8_max32
      assert property (WBM1_DAT_I == WBM1_DAT_I_INT) else $error("M1 pass-through DAT_I mismatch");
      assert property (WBM1_SEL_O_INT == {4{WBM1_SEL_O}}) else $error("M1_SEL_O_INT replication error");
      assert property (WBM1_DAT_O_INT == {4{WBM1_DAT_O}}) else $error("M1_DAT_O_INT replication error");
    end else begin : g_m1_else
      assert property (WBM1_DAT_I == WBM1_DAT_I_INT) else $error("M1 DAT_I passthrough mismatch");
      assert property (WBM1_SEL_O_INT == WBM1_SEL_O) else $error("M1 SEL_O passthrough mismatch");
      assert property (WBM1_DAT_O_INT == WBM1_DAT_O) else $error("M1 DAT_O passthrough mismatch");
    end
  endgenerate

  // Minimal functional coverage
  cover property (selected==2'd1);
  cover property (selected==2'd2);
  cover property (selected==2'd0 && WBM0_STB_O ##1 selected==2'd1);
  cover property (selected==2'd0 && !WBM0_STB_O && WBM1_STB_O ##1 selected==2'd2);
  cover property (selected==2'd0 && WBM0_STB_O && WBM1_STB_O ##1 selected==2'd1);
  cover property (selected==2'd1 && locked ##[1:$] selected==2'd0);
  cover property (selected==2'd2 && locked ##[1:$] selected==2'd0);

  generate
    if ((WBS_DAT_WIDTH == 8) && ((WBM0_DAT_WIDTH == 32) || (WBM1_DAT_WIDTH == 32))) begin
      cover property (WBS_STB_I && WBS_ADR_I[1:0]==2'b00);
      cover property (WBS_STB_I && WBS_ADR_I[1:0]==2'b01);
      cover property (WBS_STB_I && WBS_ADR_I[1:0]==2'b10);
      cover property (WBS_STB_I && WBS_ADR_I[1:0]==2'b11);
    end
  endgenerate

endmodule

bind arbiter2 arbiter2_sva #(
  .MAX_DAT_WIDTH(MAX_DAT_WIDTH),
  .WBS_DAT_WIDTH(WBS_DAT_WIDTH),
  .WBM0_DAT_WIDTH(WBM0_DAT_WIDTH),
  .WBM1_DAT_WIDTH(WBM1_DAT_WIDTH)
) arbiter2_sva_i (.*);