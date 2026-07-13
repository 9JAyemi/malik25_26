module EX_MEM_Seg_sva (
    input logic        Clk,
    input logic        stall,
    input logic        flush,
    input logic [31:0] Branch_addr,
    input logic [31:0] PC_add,
    input logic [2:0]  Condition,
    input logic        Branch,
    input logic [2:0]  PC_write,
    input logic [3:0]  Mem_Byte_Write,
    input logic [3:0]  Rd_Write_Byte_en,
    input logic        MemWBSrc,
    input logic        OverflowEn,
    input logic [31:0] MemData,
    input logic [31:0] WBData,
    input logic        Less,
    input logic        Zero,
    input logic        Overflow,
    input logic [4:0]  Rd,
    input logic [31:0] Branch_addr_out,
    input logic [31:0] PC_add_out,
    input logic [2:0]  Condition_out,
    input logic        Branch_out,
    input logic [2:0]  PC_write_out,
    input logic [3:0]  Mem_Byte_Write_out,
    input logic [3:0]  Rd_Write_Byte_en_out,
    input logic        MemWBSrc_out,
    input logic        OverflowEn_out,
    input logic [31:0] MemData_out,
    input logic [31:0] WBData_out,
    input logic        Less_out,
    input logic        Zero_out,
    input logic        Overflow_out,
    input logic [4:0]  Rd_out
);

    // flush clears all registered outputs on the next cycle.
    check_flush_clears_outputs: assert property (
        @(posedge Clk)
        flush |=> (
            (OverflowEn_out == 1'b0) &&
            (Branch_addr_out == 32'b0) &&
            (PC_add_out == 32'b0) &&
            (Condition_out == 3'b0) &&
            (Branch_out == 1'b0) &&
            (PC_write_out == 3'b0) &&
            (Mem_Byte_Write_out == 4'b0) &&
            (Rd_Write_Byte_en_out == 4'b0) &&
            (MemWBSrc_out == 1'b0) &&
            (MemData_out == 32'h0) &&
            (WBData_out == 32'b0) &&
            (Less_out == 1'b0) &&
            (Zero_out == 1'b0) &&
            (Overflow_out == 1'b0) &&
            (Rd_out == 5'b0)
        )
    );

    // stall blocks the register update when flush is low.
    check_stall_blocks_update: assert property (
        @(posedge Clk) disable iff (flush)
        stall |=> (
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

    // without flush or stall, all outputs capture their input values.
    check_update_on_no_stall_no_flush: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (
            (OverflowEn_out == $past(OverflowEn)) &&
            (Branch_addr_out == $past(Branch_addr)) &&
            (PC_add_out == $past(PC_add)) &&
            (Condition_out == $past(Condition)) &&
            (Branch_out == $past(Branch)) &&
            (PC_write_out == $past(PC_write)) &&
            (Mem_Byte_Write_out == $past(Mem_Byte_Write)) &&
            (Rd_Write_Byte_en_out == $past(Rd_Write_Byte_en)) &&
            (MemWBSrc_out == $past(MemWBSrc)) &&
            (MemData_out == $past(MemData)) &&
            (WBData_out == $past(WBData)) &&
            (Less_out == $past(Less)) &&
            (Zero_out == $past(Zero)) &&
            (Overflow_out == $past(Overflow)) &&
            (Rd_out == $past(Rd))
        )
    );

endmodule