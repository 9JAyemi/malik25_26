// SVA checkers and binders for the provided design.
// Assumes a free-running clk and active-high reset_n in your env.
// Bind connects by name to DUT signals (including internal nets).

module MUX8_1_Icontrol_chk(
  input logic clk, reset_n,
  input logic [2:0] Sel,
  input logic S0,S1,S2,S3,S4,S5,S6,S7,
  input logic out
);
  // Functional correctness when select known
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) |->
      out === (Sel[2] ? (Sel[1] ? (Sel[0]?S7:S6) : (Sel[0]?S5:S4))
                      : (Sel[1] ? (Sel[0]?S3:S2) : (Sel[0]?S1:S0)))
  );

  // No X on out when select and all data are known
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) && !$isunknown({S0,S1,S2,S3,S4,S5,S6,S7}) |-> !$isunknown(out)
  );

  // Coverage: each Sel value exercised
  genvar gi;
  generate for (gi=0; gi<8; gi++) begin : g_cov_i
    cover property (@(posedge clk) Sel==gi[2:0]);
  end endgenerate
endmodule

bind MUX8_1_Icontrol MUX8_1_Icontrol_chk u_MUX8_1_Icontrol_chk(.*);


// 8:1 SL (4-bit) MUX checker
module MUX8_1_SL_chk(
  input logic clk, reset_n,
  input logic [3:0] Sel,
  input logic [3:0] Write_Byte_En,
  input logic [3:0] S0,S1,S2,S3,S4,S5,S6,S7,
  input logic [3:0] out
);
  function automatic logic [3:0] f_mux8_sl(input logic [3:0] s,
                                           input logic [3:0] wbe,
                                           input logic [3:0] d0,d1,d2,d3,d4,d5,d6,d7);
    return s[3] ? wbe
                : (s[2] ? (s[1] ? (s[0]?d7:d6) : (s[0]?d5:d4))
                        : (s[1] ? (s[0]?d3:d2) : (s[0]?d1:d0)));
  endfunction

  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) |->
      out === f_mux8_sl(Sel,Write_Byte_En,S0,S1,S2,S3,S4,S5,S6,S7)
  );

  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) && !$isunknown({Write_Byte_En,S0,S1,S2,S3,S4,S5,S6,S7}) |-> !$isunknown(out)
  );

  // Coverage: all Sel values
  genvar gj;
  generate for (gj=0; gj<16; gj++) begin : g_cov_sl
    cover property (@(posedge clk) Sel==gj[3:0]);
  end endgenerate
endmodule

bind MUX8_1_SL MUX8_1_SL_chk u_MUX8_1_SL_chk(.*);


// 4:1 SL (4-bit) MUX checker
module MUX4_1_SL_chk(
  input logic clk, reset_n,
  input logic [1:0] Sel,
  input logic [3:0] S0,S1,S2,S3,
  input logic [3:0] out
);
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) |->
      out === (Sel[1] ? (Sel[0]?S3:S2) : (Sel[0]?S1:S0))
  );

  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(Sel) && !$isunknown({S0,S1,S2,S3}) |-> !$isunknown(out)
  );

  cover property (@(posedge clk) Sel==2'b00);
  cover property (@(posedge clk) Sel==2'b01);
  cover property (@(posedge clk) Sel==2'b10);
  cover property (@(posedge clk) Sel==2'b11);
endmodule

bind MUX4_1_SL MUX4_1_SL_chk u_MUX4_1_SL_chk(.*);


// Condition_Check checker (includes internal nets via bind)
module Condition_Check_chk(
  input logic clk, reset_n,

  // DUT ports
  input  logic [2:0] Condition, PC_Write,
  input  logic [1:0] addr,
  input  logic       MemWBSrc,
  input  logic       OverflowEn, Branch, Overflow,
  input  logic [3:0] Mem_Byte_Write,
  input  logic [3:0] Rd_Write_Byte_en,
  input  logic       Less, Zero,
  input  logic       BranchValid,
  input  logic [3:0] RdWriteEn,
  input  logic [3:0] MemWriteEn,

  // DUT internals (bound by name)
  input  logic [1:0] Right,
  input  logic       Load, Store,
  input  logic [3:0] LoadOut, StoreOut,
  input  logic       condition_out
);
  // Helpers
  function automatic logic f_mux8_ic(input logic [2:0] s,
                                     input logic d0,d1,d2,d3,d4,d5,d6,d7);
    return s[2] ? (s[1] ? (s[0]?d7:d6) : (s[0]?d5:d4))
                : (s[1] ? (s[0]?d3:d2) : (s[0]?d1:d0));
  endfunction

  function automatic logic [3:0] f_mux8_sl(input logic [3:0] s,
                                           input logic [3:0] wbe,
                                           input logic [3:0] d0,d1,d2,d3,d4,d5,d6,d7);
    return s[3] ? wbe
                : (s[2] ? (s[1] ? (s[0]?d7:d6) : (s[0]?d5:d4))
                        : (s[1] ? (s[0]?d3:d2) : (s[0]?d1:d0)));
  endfunction

  // Right mapping when PC_Write known
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(PC_Write) && (PC_Write==3'b110) |-> Right==2'b01
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(PC_Write) && (PC_Write==3'b010) |-> Right==2'b00
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown(PC_Write) && (PC_Write!=3'b110) && (PC_Write!=3'b010) |-> Right==2'b10
  );

  // Load/Store derivation from sources (4-state aware where applicable)
  assert property (@(posedge clk) (MemWBSrc===1'b1) |-> (Load===1'b1));
  assert property (@(posedge clk) (MemWBSrc===1'b0) |-> (Load===1'b0));
  assert property (@(posedge clk) (Mem_Byte_Write===4'b1111) |-> (Store===1'b1));
  assert property (@(posedge clk) !$isunknown(Mem_Byte_Write) && (Mem_Byte_Write!=4'b1111) |-> (Store===1'b0));

  // condition_out correctness
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Condition,Less,Zero}) |->
      condition_out === f_mux8_ic(Condition, 1'b0, Zero, !Zero, !Less,
                                  !(Less^Zero), (Less^Zero), Less, 1'b1)
  );

  // BranchValid handshake with condition_out
  assert property (@(posedge clk) disable iff (!reset_n)
    BranchValid |-> (Branch && condition_out)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    (Branch && condition_out) |-> BranchValid
  );

  // LoadOut and StoreOut correctness vs their MUX programming
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Right,addr}) |->
      LoadOut === f_mux8_sl({Right,addr}, Rd_Write_Byte_en,
                            4'b1111,4'b1110,4'b1100,4'b1000,4'b0001,4'b0011,4'b0111,4'b1111)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Right,addr}) |->
      StoreOut === f_mux8_sl({Right,addr}, Mem_Byte_Write,
                             4'b1111,4'b0111,4'b0011,4'b0001,4'b1000,4'b1100,4'b1110,4'b1111)
  );

  // RdWriteEn selection tree (mirrors 4-state behavior in DUT where determinable)
  assert property (@(posedge clk) disable iff (!reset_n)
    (Load===1'b1) |-> (RdWriteEn===LoadOut)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    (Load!==1'b1) && (OverflowEn===1'b0) |-> (RdWriteEn===Rd_Write_Byte_en)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    (Load!==1'b1) && (OverflowEn===1'b1) && (Overflow===1'b0) |-> (RdWriteEn===4'b1111)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    (Load!==1'b1) && (OverflowEn===1'b1) && (Overflow===1'b1) |-> (RdWriteEn===4'b0000)
  );

  // MemWriteEn selection
  assert property (@(posedge clk) disable iff (!reset_n)
    (Store===1'b1) |-> (MemWriteEn===StoreOut)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    (Store!==1'b1) |-> (MemWriteEn===4'b0000)
  );

  // No X on key outputs when controls and sources are known
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Branch,condition_out}) |-> !$isunknown(BranchValid)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Load,OverflowEn,Overflow,Rd_Write_Byte_en,LoadOut}) |-> !$isunknown(RdWriteEn)
  );
  assert property (@(posedge clk) disable iff (!reset_n)
    !$isunknown({Store,StoreOut}) |-> !$isunknown(MemWriteEn)
  );

  // Coverage
  cover property (@(posedge clk) PC_Write==3'b110 && Right==2'b01);
  cover property (@(posedge clk) PC_Write==3'b010 && Right==2'b00);
  cover property (@(posedge clk) !$isunknown(PC_Write) && PC_Write!=3'b110 && PC_Write!=3'b010 && Right==2'b10);

  genvar ck;
  generate for (ck=0; ck<8; ck++) begin : g_cov_cond
    cover property (@(posedge clk) Condition==ck[2:0]);
  end endgenerate

  cover property (@(posedge clk) (Load===1'b1) && (RdWriteEn===LoadOut));
  cover property (@(posedge clk) (Load!==1'b1) && (OverflowEn===1'b0) && (RdWriteEn===Rd_Write_Byte_en));
  cover property (@(posedge clk) (Load!==1'b1) && (OverflowEn===1'b1) && (Overflow===1'b0) && (RdWriteEn==4'b1111));
  cover property (@(posedge clk) (Load!==1'b1) && (OverflowEn===1'b1) && (Overflow===1'b1) && (RdWriteEn==4'b0000));

  cover property (@(posedge clk) (Store===1'b1) && (MemWriteEn===StoreOut));
  cover property (@(posedge clk) (Store!==1'b1) && (MemWriteEn==4'b0000));

  cover property (@(posedge clk) Branch && condition_out && BranchValid);
endmodule

bind Condition_Check Condition_Check_chk u_Condition_Check_chk(
  .* // includes internals by name in this scope
);