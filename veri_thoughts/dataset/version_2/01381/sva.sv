module controlunit_sva (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [5:0]  imemout,
    input  logic        brnch,
    input  logic        memorywrite,
    input  logic        memoryread,
    input  logic        alusrc,
    input  logic        regw,
    input  logic        regdst,
    input  logic        aluop,
    input  logic        memtoreg
);
    localparam logic [5:0] OPC_RTYPE = 6'b000000;
    localparam logic [5:0] OPC_LW    = 6'b100011;
    localparam logic [5:0] OPC_SW    = 6'b101011;
    localparam logic [5:0] OPC_BEQ   = 6'b000100;

    // R-type decode drives exact outputs.
    check_decode_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OPC_RTYPE) |-> (brnch==1'b0 && memorywrite==1'b0 && memoryread==1'b0 && alusrc==1'b0 && regw==1'b1 && regdst==1'b1 && aluop==1'b1 && memtoreg==1'b1)
    );

    // LW decode drives exact outputs.
    check_decode_lw: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OPC_LW) |-> (brnch==1'b0 && memorywrite==1'b0 && memoryread==1'b1 && alusrc==1'b1 && regw==1'b1 && regdst==1'b0 && aluop==1'b0 && memtoreg==1'b0)
    );

    // SW decode drives exact outputs.
    check_decode_sw: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OPC_SW) |-> (brnch==1'b0 && memorywrite==1'b1 && memoryread==1'b0 && alusrc==1'b1 && regw==1'b0 && regdst==1'b0 && aluop==1'b0 && memtoreg==1'b0)
    );

    // BEQ decode drives exact outputs.
    check_decode_beq: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OPC_BEQ) |-> (brnch==1'b1 && memorywrite==1'b0 && memoryread==1'b0 && alusrc==1'b0 && regw==1'b0 && regdst==1'b0 && aluop==1'b0 && memtoreg==1'b0)
    );

    // Default decode (all other opcodes) drives all zeros.
    check_decode_default: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((imemout != OPC_RTYPE) && (imemout != OPC_LW) && (imemout != OPC_SW) && (imemout != OPC_BEQ))
        |-> (brnch==1'b0 && memorywrite==1'b0 && memoryread==1'b0 && alusrc==1'b0 && regw==1'b0 && regdst==1'b0 && aluop==1'b0 && memtoreg==1'b0)
    );

    // Read and write to memory are never both asserted.
    check_rd_wr_mutex: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(memoryread && memorywrite)
    );

    // ALUOP high occurs only for R-type.
    check_aluop_only_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        aluop |-> (imemout == OPC_RTYPE)
    );

    // REGDST high occurs only for R-type.
    check_regdst_only_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        regdst |-> (imemout == OPC_RTYPE)
    );

    // MEMTOREG high occurs only for R-type.
    check_memtoreg_only_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        memtoreg |-> (imemout == OPC_RTYPE)
    );

    // ALUSRC high occurs only for LW or SW.
    check_alusrc_lw_or_sw: assert property (
        @(posedge clk) disable iff (!reset_n)
        alusrc |-> ((imemout == OPC_LW) || (imemout == OPC_SW))
    );

    // REGW high occurs only for R-type or LW.
    check_regw_rtype_or_lw: assert property (
        @(posedge clk) disable iff (!reset_n)
        regw |-> ((imemout == OPC_RTYPE) || (imemout == OPC_LW))
    );

    // MEMORYREAD implies LW opcode.
    check_memoryread_implies_lw: assert property (
        @(posedge clk) disable iff (!reset_n)
        memoryread |-> (imemout == OPC_LW)
    );

    // MEMORYWRITE implies SW opcode.
    check_memorywrite_implies_sw: assert property (
        @(posedge clk) disable iff (!reset_n)
        memorywrite |-> (imemout == OPC_SW)
    );

    // BRNCH implies BEQ opcode and no memory access.
    check_branch_implies_beq_no_mem: assert property (
        @(posedge clk) disable iff (!reset_n)
        brnch |-> ((imemout == OPC_BEQ) && !memoryread && !memorywrite)
    );

    // MEMTOREG high implies REGW high and no MEMORYREAD.
    check_memtoreg_implies_regw: assert property (
        @(posedge clk) disable iff (!reset_n)
        memtoreg |-> (regw && !memoryread)
    );

    // If IMEMOUT is stable across cycles, outputs remain stable.
    check_stability_when_input_stable: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == $past(imemout)) |-> (brnch==$past(brnch) && memorywrite==$past(memorywrite) && memoryread==$past(memoryread) && alusrc==$past(alusrc) && regw==$past(regw) && regdst==$past(regdst) && aluop==$past(aluop) && memtoreg==$past(memtoreg))
    );
endmodule