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
    input logic [3:0] Rd_Write_Byte_en,
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
    input logic [3:0] Rd_Write_Byte_en_out,
    input logic MemWBSrc_out,
    input logic OverflowEn_out,
    input logic [31:0] MemData_out,
    input logic [31:0] WBData_out,
    input logic Less_out,
    input logic Zero_out,
    input logic Overflow_out,
    input logic [4:0] Rd_out
);

    // flush clears all stored outputs on the next cycle.
    check_flush_clears_outputs: assert property (
        @(posedge Clk)
        flush |=> (
            (Branch_addr_out == 32'h0) &&
            (PC_add_out == 32'h0) &&
            (Condition_out == 3'b000) &&
            (Branch_out == 1'b0) &&
            (PC_write_out == 3'b000) &&
            (Mem_Byte_Write_out == 4'b0000) &&
            (Rd_Write_Byte_en_out == 4'b0000) &&
            (MemWBSrc_out == 1'b0) &&
            (OverflowEn_out == 1'b0) &&
            (MemData_out == 32'h0) &&
            (WBData_out == 32'h0) &&
            (Less_out == 1'b0) &&
            (Zero_out == 1'b0) &&
            (Overflow_out == 1'b0) &&
            (Rd_out == 5'b0)
        )
    );

    // stall blocks the update when flush is not asserted.
    check_stall_blocks_update: assert property (
        @(posedge Clk) disable iff (flush)
        stall |=> (
            (Branch_addr_out == $past(Branch_addr_out)) &&
            (PC_add_out == $past(PC_add_out)) &&
            (Condition_out == $past(Condition_out)) &&
            (Branch_out == $past(Branch_out)) &&
            (PC_write_out == $past(PC_write_out)) &&
            (Mem_Byte_Write_out == $past(Mem_Byte_Write_out)) &&
            (Rd_Write_Byte_en_out == $past(Rd_Write_Byte_en_out)) &&
            (MemWBSrc_out == $past(MemWBSrc_out)) &&
            (OverflowEn_out == $past(OverflowEn_out)) &&
            (MemData_out == $past(MemData_out)) &&
            (WBData_out == $past(WBData_out)) &&
            (Less_out == $past(Less_out)) &&
            (Zero_out == $past(Zero_out)) &&
            (Overflow_out == $past(Overflow_out)) &&
            (Rd_out == $past(Rd_out))
        )
    );

    // overflow enable is captured when not stalled and not flushing.
    check_overflowen_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (OverflowEn_out == $past(OverflowEn))
    );

    // branch address is captured when not stalled and not flushing.
    check_branch_addr_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Branch_addr_out == $past(Branch_addr))
    );

    // pc add is captured when not stalled and not flushing.
    check_pc_add_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (PC_add_out == $past(PC_add))
    );

    // condition is captured when not stalled and not flushing.
    check_condition_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Condition_out == $past(Condition))
    );

    // branch signal is captured when not stalled and not flushing.
    check_branch_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Branch_out == $past(Branch))
    );

    // pc write is captured when not stalled and not flushing.
    check_pc_write_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (PC_write_out == $past(PC_write))
    );

    // memory byte write is captured when not stalled and not flushing.
    check_mem_byte_write_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Mem_Byte_Write_out == $past(Mem_Byte_Write))
    );

    // rd write byte enable is captured when not stalled and not flushing.
    check_rd_write_byte_en_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Rd_Write_Byte_en_out == $past(Rd_Write_Byte_en))
    );

    // memory writeback source is captured when not stalled and not flushing.
    check_memwb_src_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (MemWBSrc_out == $past(MemWBSrc))
    );

    // memory data is captured when not stalled and not flushing.
    check_memdata_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (MemData_out == $past(MemData))
    );

    // wb data is captured when not stalled and not flushing.
    check_wbdata_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (WBData_out == $past(WBData))
    );

    // less-than result is captured when not stalled and not flushing.
    check_less_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Less_out == $past(Less))
    );

    // zero result is captured when not stalled and not flushing.
    check_zero_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Zero_out == $past(Zero))
    );

    // overflow result is captured when not stalled and not flushing.
    check_overflow_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Overflow_out == $past(Overflow))
    );

    // rd is captured when not stalled and not flushing.
    check_rd_capture: assert property (
        @(posedge Clk) disable iff (flush)
        !stall |=> (Rd_out == $past(Rd))
    );

endmodule