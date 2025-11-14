// SVA for Mux4_1_3
module Mux4_1_3_sva (
  input logic [2:0] Data0,Data1,Data2,Data3,
  input logic [1:0]  Sel,
  input logic [2:0]  Data
);
  // Functional correctness
  assert property (@(*) (Sel==2'b00) |-> (Data===Data0));
  assert property (@(*) (Sel==2'b01) |-> (Data===Data1));
  assert property (@(*) (Sel==2'b10) |-> (Data===Data2));
  assert property (@(*) (Sel==2'b11) |-> (Data===Data3));

  // Coverage: all select paths taken and deliver the right data
  cover property (@(*) Sel==2'b00 && Data===Data0);
  cover property (@(*) Sel==2'b01 && Data===Data1);
  cover property (@(*) Sel==2'b10 && Data===Data2);
  cover property (@(*) Sel==2'b11 && Data===Data3);
endmodule

bind Mux4_1_3 Mux4_1_3_sva mux4_1_3_sva_bind (.*);


// SVA for HazardControl
module HazardControl_sva (
  input  logic        EX_MEM_Branch,
  input  logic        Jump,
  input  logic        MemWBSrc, RsRead, RtRead,
  input  logic [4:0]  Rs_From_IF_ID, Rt_From_IF_ID,
  input  logic [4:0]  Rt_From_ID_EX,
  input  logic        IF_ID_stall, ID_EX_stall, EX_MEM_stall, MEM_WB_stall,
  input  logic        IF_ID_flush, ID_EX_flush, EX_MEM_flush, MEM_WB_flush,
  input  logic [2:0]  PCSrc,
  input  logic        LoadUse // internal net in DUT
);
  // Helper reductions for exact-1 checks used by DUT
  wire j_t = (Jump          === 1'b1);
  wire b_t = (EX_MEM_Branch === 1'b1);

  // Load-use definition equivalence
  assert property (@(*)
    LoadUse == ( (((RsRead===1'b1) && (Rt_From_ID_EX===Rs_From_IF_ID)) ||
                   ((RtRead===1'b1) && (Rt_From_ID_EX===Rt_From_IF_ID))) &&
                  (MemWBSrc===1'b1) )
  );

  // Stall/flush behavior
  assert property (@(*) IF_ID_stall == LoadUse);
  assert property (@(*) ID_EX_stall == 1'b0);
  assert property (@(*) EX_MEM_stall == 1'b0);
  assert property (@(*) MEM_WB_stall == 1'b0);

  assert property (@(*) IF_ID_flush == 1'b0);
  assert property (@(*) ID_EX_flush == (j_t || b_t || LoadUse));
  assert property (@(*) EX_MEM_flush == b_t);
  assert property (@(*) MEM_WB_flush == 1'b0);

  // PCSrc encoding from Jump/Branch truth table (matches mux instantiation)
  assert property (@(*) (!j_t && !b_t) |-> (PCSrc==3'b000));
  assert property (@(*) ( b_t && !j_t) |-> (PCSrc==3'b010));
  assert property (@(*) ( j_t && !b_t) |-> (PCSrc==3'b001));
  assert property (@(*) ( j_t &&  b_t) |-> (PCSrc==3'b010));
  assert property (@(*) PCSrc inside {3'b000,3'b001,3'b010});

  // No-X on controls produced by exact compares
  assert property (@(*) !$isunknown({IF_ID_stall,ID_EX_stall,EX_MEM_stall,MEM_WB_stall,
                                     IF_ID_flush,ID_EX_flush,EX_MEM_flush,MEM_WB_flush,PCSrc}));

  // Coverage: hazard types, control actions, PCSrc encodings
  cover property (@(*) (RsRead===1'b1) && (MemWBSrc===1'b1) && (Rt_From_ID_EX===Rs_From_IF_ID) && LoadUse);
  cover property (@(*) (RtRead===1'b1) && (MemWBSrc===1'b1) && (Rt_From_ID_EX===Rt_From_IF_ID) && LoadUse);

  cover property (@(*) j_t && !b_t && PCSrc==3'b001 && ID_EX_flush);
  cover property (@(*) b_t && !j_t && PCSrc==3'b010 && EX_MEM_flush && ID_EX_flush);
  cover property (@(*) !j_t && !b_t && !LoadUse && PCSrc==3'b000 &&
                           !IF_ID_stall && !ID_EX_flush && !EX_MEM_flush);

  cover property (@(*) PCSrc==3'b000);
  cover property (@(*) PCSrc==3'b001);
  cover property (@(*) PCSrc==3'b010);
endmodule

bind HazardControl HazardControl_sva hazardcontrol_sva_bind (.*);