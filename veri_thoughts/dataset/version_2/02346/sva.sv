module controlunit_sva (
    // Sampling clock/reset (RTL has no clock/reset; combinational decode; used only for property sampling/masking)
    input logic clk,
    input logic reset_n,

    // DUT ports as inputs
    input logic [5:0] imemout,
    input logic brnch,
    input logic memorywrite,
    input logic memoryread,
    input logic alusrc,
    input logic regw,
    input logic regdst,
    input logic aluop,
    input logic memtoreg
);

    // Opcode aliases
    localparam logic [5:0] OP_RTYPE = 6'b000000;
    localparam logic [5:0] OP_LW    = 6'b100011;
    localparam logic [5:0] OP_SW    = 6'b101011;
    localparam logic [5:0] OP_BEQ   = 6'b000100;

    ///// Exact decode mapping /////
    // Outputs for R-type opcode (000000).
    decode_rtype_match: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OP_RTYPE) |-> (brnch == 1'b0) && (memorywrite == 1'b0) && (memoryread == 1'b0) &&
                                 (alusrc == 1'b0) && (regw == 1'b1) && (regdst == 1'b1) &&
                                 (aluop == 1'b1) && (memtoreg == 1'b1)
    );

    // Outputs for LW opcode (100011).
    decode_lw_match: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OP_LW) |-> (brnch == 1'b0) && (memorywrite == 1'b0) && (memoryread == 1'b1) &&
                              (alusrc == 1'b1) && (regw == 1'b1) && (regdst == 1'b0) &&
                              (aluop == 1'b0) && (memtoreg == 1'b0)
    );

    // Outputs for SW opcode (101011).
    decode_sw_match: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OP_SW) |-> (brnch == 1'b0) && (memorywrite == 1'b1) && (memoryread == 1'b0) &&
                              (alusrc == 1'b1) && (regw == 1'b0) && (regdst == 1'b0) &&
                              (aluop == 1'b0) && (memtoreg == 1'b0)
    );

    // Outputs for BEQ opcode (000100).
    decode_beq_match: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout == OP_BEQ) |-> (brnch == 1'b1) && (memorywrite == 1'b0) && (memoryread == 1'b0) &&
                              (alusrc == 1'b0) && (regw == 1'b0) && (regdst == 1'b0) &&
                              (aluop == 1'b0) && (memtoreg == 1'b0)
    );

    // Outputs for all other opcodes: all control signals LOW.
    decode_default_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (imemout != OP_RTYPE && imemout != OP_LW && imemout != OP_SW && imemout != OP_BEQ)
        |-> (brnch == 1'b0) && (memorywrite == 1'b0) && (memoryread == 1'b0) &&
            (alusrc == 1'b0) && (regw == 1'b0) && (regdst == 1'b0) &&
            (aluop == 1'b0) && (memtoreg == 1'b0)
    );

    ///// Invariants implied by the decode /////
    // Read and write to memory are never asserted together.
    check_memread_write_mutex: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(memoryread && memorywrite)
    );

    // BRNCH can be HIGH only for BEQ.
    unique_brnch_on_beq: assert property (
        @(posedge clk) disable iff (!reset_n)
        brnch |-> (imemout == OP_BEQ)
    );

    // MEMORYREAD can be HIGH only for LW.
    unique_memoryread_on_lw: assert property (
        @(posedge clk) disable iff (!reset_n)
        memoryread |-> (imemout == OP_LW)
    );

    // MEMORYWRITE can be HIGH only for SW.
    unique_memorywrite_on_sw: assert property (
        @(posedge clk) disable iff (!reset_n)
        memorywrite |-> (imemout == OP_SW)
    );

    // MEMTOREG can be HIGH only for R-type.
    unique_memtoreg_on_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        memtoreg |-> (imemout == OP_RTYPE)
    );

    // REGDST can be HIGH only for R-type.
    unique_regdst_on_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        regdst |-> (imemout == OP_RTYPE)
    );

    // ALUOP can be HIGH only for R-type.
    unique_aluop_on_rtype: assert property (
        @(posedge clk) disable iff (!reset_n)
        aluop |-> (imemout == OP_RTYPE)
    );

    // REGW can be HIGH only for R-type or LW.
    unique_regw_on_rtype_or_lw: assert property (
        @(posedge clk) disable iff (!reset_n)
        regw |-> ((imemout == OP_RTYPE) || (imemout == OP_LW))
    );

    // ALUSRC can be HIGH only for LW or SW.
    unique_alusrc_on_lw_or_sw: assert property (
        @(posedge clk) disable iff (!reset_n)
        alusrc |-> ((imemout == OP_LW) || (imemout == OP_SW))
    );

endmodule