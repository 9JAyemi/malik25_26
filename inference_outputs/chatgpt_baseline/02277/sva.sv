module EX_MEM_Seg_sva (
    input logic Clk,
    input logic stall,
    input logic flush,

    input logic [31:0] Branch_addr, PC_add,
    input logic [2:0] Condition,
    input logic Branch,
    input logic [2:0] PC_write,
    input logic [3:0] Mem_Byte_Write, Rd_Write_Byte_en,
    input logic MemWBSrc, OverflowEn,
    input logic [31:0] MemData, WBData,
    input logic Less, Zero, Overflow,
    input logic [4:0] Rd,

    input logic [31:0] Branch_addr_out, PC_add_out,
    input logic [2:0] Condition_out,
    input logic Branch_out,
    input logic [2:0] PC_write_out,
    input logic [3:0] Mem_Byte_Write_out, Rd_Write_Byte_en_out,
    input logic MemWBSrc_out, OverflowEn_out,
    input logic [31:0] MemData_out, WBData_out,
    input logic Less_out, Zero_out, Overflow_out,
    input logic [4:0] Rd_out
);
    // Analysis: Clock=Clk (posedge). No explicit reset; flush is synchronous active-high clear.
    // Sequential pipeline register: flush clears, stall holds, else pass-through.

    // On flush, all pipeline outputs are cleared to zero in the same cycle.
    check_flush_clears_all_outputs: assert property (
        @(posedge Clk)
            flush |-> (
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

    // When stalled (and not flushing), all outputs hold their previous values.
    check_stall_holds_all_outputs: assert property (
        @(posedge Clk)
            (!flush && stall) |-> $stable({
                OverflowEn_out, Branch_addr_out, PC_add_out, Condition_out, Branch_out,
                PC_write_out, Mem_Byte_Write_out, Rd_Write_Byte_en_out, MemWBSrc_out,
                MemData_out, WBData_out, Less_out, Zero_out, Overflow_out, Rd_out
            })
    );

    // On normal advance (!flush && !stall), outputs sample corresponding inputs.
    check_update_transfers_all_outputs: assert property (
        @(posedge Clk)
            (!flush && !stall) |-> (
                {
                    OverflowEn_out, Branch_addr_out, PC_add_out, Condition_out, Branch_out,
                    PC_write_out, Mem_Byte_Write_out, Rd_Write_Byte_en_out, MemWBSrc_out,
                    MemData_out, WBData_out, Less_out, Zero_out, Overflow_out, Rd_out
                } == {
                    OverflowEn,     Branch_addr,     PC_add,     Condition,     Branch,
                    PC_write,       Mem_Byte_Write,  Rd_Write_Byte_en,          MemWBSrc,
                    MemData,        WBData,          Less,       Zero,          Overflow, Rd
                }
            )
    );

    // Outputs can only change on cycles with flush or when not stalled.
    check_outputs_change_only_when_allowed: assert property (
        @(posedge Clk)
            $changed({
                OverflowEn_out, Branch_addr_out, PC_add_out, Condition_out, Branch_out,
                PC_write_out, Mem_Byte_Write_out, Rd_Write_Byte_en_out, MemWBSrc_out,
                MemData_out, WBData_out, Less_out, Zero_out, Overflow_out, Rd_out
            }) |-> (flush || !stall)
    );

    // Flush has priority over stall: if both true, outputs are cleared.
    check_flush_priority_over_stall: assert property (
        @(posedge Clk)
            (flush && stall) |-> (
                {
                    OverflowEn_out, Branch_addr_out, PC_add_out, Condition_out, Branch_out,
                    PC_write_out, Mem_Byte_Write_out, Rd_Write_Byte_en_out, MemWBSrc_out,
                    MemData_out, WBData_out, Less_out, Zero_out, Overflow_out, Rd_out
                } == {
                    1'b0, 32'b0, 32'b0, 3'b0, 1'b0,
                    3'b0, 4'b0, 4'b0, 1'b0,
                    32'h0, 32'b0, 1'b0, 1'b0, 1'b0, 5'b0
                }
            )
    );

    // Data/address buses pass through on advance.
    check_data_buses_update_on_advance: assert property (
        @(posedge Clk)
            (!flush && !stall) |-> (
                (Branch_addr_out == Branch_addr) &&
                (PC_add_out == PC_add) &&
                (MemData_out == MemData) &&
                (WBData_out == WBData)
            )
    );

    // Control/flag bits pass through on advance.
    check_flags_update_on_advance: assert property (
        @(posedge Clk)
            (!flush && !stall) |-> (
                (Less_out == Less) &&
                (Zero_out == Zero) &&
                (Overflow_out == Overflow) &&
                (OverflowEn_out == OverflowEn) &&
                (Branch_out == Branch) &&
                (MemWBSrc_out == MemWBSrc)
            )
    );

    // Byte-enable and PC_write fields pass through on advance.
    check_byte_enables_update_on_advance: assert property (
        @(posedge Clk)
            (!flush && !stall) |-> (
                (Mem_Byte_Write_out == Mem_Byte_Write) &&
                (Rd_Write_Byte_en_out == Rd_Write_Byte_en) &&
                (PC_write_out == PC_write)
            )
    );

    // Destination register index passes through on advance.
    check_rd_update_on_advance: assert property (
        @(posedge Clk)
            (!flush && !stall) |-> (Rd_out == Rd)
    );
endmodule