module EX_MEM_Seg_sva (
    input logic Clk,
    input logic stall,
    input logic flush,

    input logic [31:0] Branch_addr,
    input logic [31:0] PC_add,
    input logic [2:0] Condition,
    input logic Branch,
    input logic [2:0] PC_write,
    input logic [3:0] Mem_Byte_Write,
    input logic [4:0] Rd_Write_Byte_en,
    input logic MemWBSrc,
    input logic OverflowEn,
    input logic [31:0] MemData,
    input logic [31:0] WBData,
    input logic Less,
    input logic Zero,
    input logic Overflow,
    input logic [4:0] Rd,

    input logic [31:0] Branch_addr_out,
    input logic [31:0] PC_add_out,
    input logic [2:0] Condition_out,
    input logic Branch_out,
    input logic [2:0] PC_write_out,
    input logic [3:0] Mem_Byte_Write_out,
    input logic [4:0] Rd_Write_Byte_en_out,
    input logic MemWBSrc_out,
    input logic OverflowEn_out,
    input logic [31:0] MemData_out,
    input logic [31:0] WBData_out,
    input logic Less_out,
    input logic Zero_out,
    input logic Overflow_out,
    input logic [4:0] Rd_out
);

// Flush clears all outputs on the next cycle.
    check_flush_clears_outputs: assert property (
        @(posedge Clk) flush |=> (
            (OverflowEn_out == 1'b0) &&
            (Branch_addr_out == 32'b0) &&
            (PC_add_out == 32'b0) &&
            (Condition_out == 3'b0) &&
            (Branch_out == 1'b0) &&
            (PC_write_out == 3'b0) &&
            (Mem_Byte_Write_out == 4'b0) &&
            (Rd_Write_Byte_en_out == 5'b0) &&
            (MemWBSrc_out == 1'b0) &&
            (MemData_out == 32'h0) &&
            (WBData_out == 32'b0) &&
            (Less_out == 1'b0) &&
            (Zero_out == 1'b0) &&
            (Overflow_out == 1'b0) &&
            (Rd_out == 5'b0)
        )
    );

// When not stalled, outputs capture the current cycle's inputs.
    check_capture_when_not_stalled: assert property (
        @(posedge Clk) disable iff (flush) (!stall) |=> (
            (OverflowEn_out == OverflowEn) &&
            (Branch_addr_out == Branch_addr) &&
            (PC_add_out == PC_add) &&
            (Condition_out == Condition) &&
            (Branch_out == Branch) &&
            (PC_write_out == PC_write) &&
            (Mem_Byte_Write_out == Mem_Byte_Write) &&
            (Rd_Write_Byte_en_out == Rd_Write_Byte_en) &&
            (MemWBSrc_out == MemWBSrc) &&
            (MemData_out == MemData) &&
            (WBData_out == WBData) &&
            (Less_out == Less) &&
            (Zero_out == Zero) &&
            (Overflow_out == Overflow) &&
            (Rd_out == Rd)
        )
    );

// When stalled, outputs hold their previous values.
    check_hold_when_stalled: assert property (
        @(posedge Clk) disable iff (flush) stall |=> (
            (OverflowEn_out == $past(OverflowEn_out)) &&
            (Branch_addr_out == $past(Branch_addr_out)) &&
            (PC_add_out == $past(PC_add_out)) &&
            (Condition_out == $past(Condition_out)) &&
            (Branch_out == $past(Branch_out)) &&
            (PC_write_out == $past(PC_write_out)) &&
            (Mem_Byte_Write_out == $past(Mem_Byte_Write_out)) &&
            (Rd_Write_Byte_en_out == $past(Rd_Write_Byte_en_out)) &&
            (MemWBSrc_out == $past(MemWBSrc_out)) &&
            (MemData_out == $past(MemData_out)) &&
            (WBData_out == $past(WBData_out)) &&
            (Less_out == $past(Less_out)) &&
            (Zero_out == $past(Zero_out)) &&
            (Overflow_out == $past(Overflow_out)) &&
            (Rd_out == $past(Rd_out))
        )
    );

endmodule
