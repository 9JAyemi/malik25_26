module EX_MEM_Seg_sva (
    input logic Branch,
    input logic Branch_addr,
    input logic Branch_addr_out,
    input logic Branch_out,
    input logic Clk,
    input logic Condition,
    input logic Condition_out,
    input logic Less,
    input logic Less_out,
    input logic MemData,
    input logic MemData_out,
    input logic MemWBSrc,
    input logic MemWBSrc_out,
    input logic Mem_Byte_Write,
    input logic Mem_Byte_Write_out,
    input logic Overflow,
    input logic OverflowEn,
    input logic OverflowEn_out,
    input logic Overflow_out,
    input logic PC_add,
    input logic PC_add_out,
    input logic PC_write,
    input logic PC_write_out,
    input logic Rd,
    input logic Rd_Write_Byte_en,
    input logic Rd_Write_Byte_en_out,
    input logic Rd_out,
    input logic WBData,
    input logic WBData_out,
    input logic Zero,
    input logic Zero_out,
    input logic flush,
    input logic stall,
    input logic b0,
    input logic h0
);

property ResetSynceotid; @(posedge Clk) (flush) |-> (OverflowEn_out == 1'b0) && (Branch_addr_out == 32'b0) && (PC_add_out == 32'b0) && (Condition_out == 3'b0) && (Branch_out == 1'b0) && (PC_write_out == 3'b0) && (Mem_Byte_Write_out == 4'b0) && (Rd_Write_Byte_en_out == 4'b0) && (MemWBSrc_out == 1'b0) && (MemData_out == 32'h0) && (WBData_out == 32'b0) && (Less_out == 1'b0) && (Zero_out == 1'b0) && (Overflow_out  == 1'b0) && (Rd_out == 5'b0) ;endproperty
assert property (ResetSynceotid);

property SyncValideotid; @(posedge Clk) ( !flush ) && (  ~stall ) |-> (OverflowEn_out == OverflowEn) && (Branch_addr_out == Branch_addr) && (PC_add_out == PC_add) && (Condition_out == Condition) && (Branch_out == Branch) && (PC_write_out == PC_write) && (Mem_Byte_Write_out == Mem_Byte_Write) && (Rd_Write_Byte_en_out == Rd_Write_Byte_en) && (MemWBSrc_out == MemWBSrc) && (MemData_out == MemData) && (WBData_out == WBData) && (Less_out == Less) && (Zero_out == Zero) && (Overflow_out  == Overflow) && (Rd_out == Rd) ;endproperty
assert property (SyncValideotid);

endmodule