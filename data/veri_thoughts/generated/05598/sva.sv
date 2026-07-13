module control_sva(
    input logic        clk,
    input logic [5:0]  opcode,
    input logic        branch_eq,
    input logic        branch_ne,
    input logic [1:0]  aluop,
    input logic        memread,
    input logic        memwrite,
    input logic        memtoreg,
    input logic        regdst,
    input logic        regwrite,
    input logic        alusrc,
    input logic        jump
);

    localparam [5:0] OPC_LW    = 6'b100011;
    localparam [5:0] OPC_ADDI  = 6'b001000;
    localparam [5:0] OPC_BEQ   = 6'b000100;
    localparam [5:0] OPC_SW    = 6'b101011;
    localparam [5:0] OPC_BNE   = 6'b000101;
    localparam [5:0] OPC_RTYPE = 6'b000000;
    localparam [5:0] OPC_J     = 6'b000010;

    // LW opcode selects the implemented load controls.
    check_lw_decode: assert property (
        @(posedge clk)
        (opcode == OPC_LW) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b00 &&
            memread   == 1'b1 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b1 &&
            regdst    == 1'b0 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b1 &&
            jump      == 1'b0
        )
    );

    // ADDI opcode selects the implemented immediate ALU controls.
    check_addi_decode: assert property (
        @(posedge clk)
        (opcode == OPC_ADDI) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b00 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b0 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b1 &&
            jump      == 1'b0
        )
    );

    // BEQ opcode selects the implemented branch-equal controls.
    check_beq_decode: assert property (
        @(posedge clk)
        (opcode == OPC_BEQ) |-> (
            branch_eq == 1'b1 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b01 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b0 &&
            alusrc    == 1'b0 &&
            jump      == 1'b0
        )
    );

    // SW opcode selects the implemented store controls.
    check_sw_decode: assert property (
        @(posedge clk)
        (opcode == OPC_SW) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b00 &&
            memread   == 1'b0 &&
            memwrite  == 1'b1 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b0 &&
            alusrc    == 1'b1 &&
            jump      == 1'b0
        )
    );

    // BNE opcode selects the implemented branch-not-equal controls.
    check_bne_decode: assert property (
        @(posedge clk)
        (opcode == OPC_BNE) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b1 &&
            aluop     == 2'b01 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b0 &&
            alusrc    == 1'b0 &&
            jump      == 1'b0
        )
    );

    // R-type opcode leaves all controls at their default values.
    check_rtype_decode: assert property (
        @(posedge clk)
        (opcode == OPC_RTYPE) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b10 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b0 &&
            jump      == 1'b0
        )
    );

    // J opcode only raises jump and otherwise keeps defaults.
    check_jump_decode: assert property (
        @(posedge clk)
        (opcode == OPC_J) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b10 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b0 &&
            jump      == 1'b1
        )
    );

    // Any unlisted opcode keeps the default control values.
    check_unlisted_opcode_defaults: assert property (
        @(posedge clk)
        (opcode != OPC_LW &&
         opcode != OPC_ADDI &&
         opcode != OPC_BEQ &&
         opcode != OPC_SW &&
         opcode != OPC_BNE &&
         opcode != OPC_RTYPE &&
         opcode != OPC_J) |-> (
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            aluop     == 2'b10 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b0 &&
            regdst    == 1'b1 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b0 &&
            jump      == 1'b0
        )
    );

    // branch_eq can only be asserted by the BEQ decode.
    check_branch_eq_only_beq: assert property (
        @(posedge clk)
        branch_eq |-> (
            opcode    == OPC_BEQ &&
            branch_ne == 1'b0 &&
            aluop     == 2'b01 &&
            regwrite  == 1'b0 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            jump      == 1'b0
        )
    );

    // branch_ne can only be asserted by the BNE decode.
    check_branch_ne_only_bne: assert property (
        @(posedge clk)
        branch_ne |-> (
            opcode    == OPC_BNE &&
            branch_eq == 1'b0 &&
            aluop     == 2'b01 &&
            regwrite  == 1'b0 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            jump      == 1'b0
        )
    );

    // memread can only be asserted by the LW decode.
    check_memread_only_lw: assert property (
        @(posedge clk)
        memread |-> (
            opcode    == OPC_LW &&
            memwrite  == 1'b0 &&
            memtoreg  == 1'b1 &&
            regdst    == 1'b0 &&
            regwrite  == 1'b1 &&
            alusrc    == 1'b1 &&
            jump      == 1'b0
        )
    );

    // memwrite can only be asserted by the SW decode.
    check_memwrite_only_sw: assert property (
        @(posedge clk)
        memwrite |-> (
            opcode    == OPC_SW &&
            memread   == 1'b0 &&
            memtoreg  == 1'b0 &&
            regwrite  == 1'b0 &&
            alusrc    == 1'b1 &&
            jump      == 1'b0
        )
    );

    // jump can only be asserted by the J decode.
    check_jump_only_jump_opcode: assert property (
        @(posedge clk)
        jump |-> (
            opcode    == OPC_J &&
            branch_eq == 1'b0 &&
            branch_ne == 1'b0 &&
            memread   == 1'b0 &&
            memwrite  == 1'b0 &&
            alusrc    == 1'b0
        )
    );

endmodule