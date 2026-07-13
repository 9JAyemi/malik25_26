module control_sva (
    input logic CLK,
    input logic RESETn,
    input logic [2:0] OP,
    input logic CISEL,
    input logic BSEL,
    input logic [1:0] OSEL,
    input logic SHIFT_LA,
    input logic SHIFT_LR,
    input logic LOGICAL_OP
);

    // SUB decode on CISEL/BSEL from OP[2:0] == 3'b001.
    check_cisel_bsel_decode: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (CISEL == (OP == 3'b001)) && (BSEL == (OP == 3'b001))
    );

    // For ADD (000): OSEL=00, no shifts, not logical, CISEL/BSEL=0.
    check_add_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b000) |-> (OSEL == 2'b00) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For SUB (001): OSEL=00, no shifts, not logical, CISEL/BSEL=1.
    check_sub_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b001) |-> (OSEL == 2'b00) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b1) && (BSEL == 1'b1)
    );

    // For SRA (010): OSEL=01, LA=1, LR=1, not logical, CISEL/BSEL=0.
    check_sra_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b010) |-> (OSEL == 2'b01) && (SHIFT_LA == 1'b1) && (SHIFT_LR == 1'b1) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For SRL (011): OSEL=01, LA=0, LR=1, not logical, CISEL/BSEL=0.
    check_srl_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b011) |-> (OSEL == 2'b01) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b1) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For SLL (100): OSEL=01, LA=1, LR=0, not logical, CISEL/BSEL=0.
    check_sll_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b100) |-> (OSEL == 2'b01) && (SHIFT_LA == 1'b1) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For AND (101): OSEL=10, no shifts, logical_op=1, CISEL/BSEL=0.
    check_and_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b101) |-> (OSEL == 2'b10) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b1) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For OR (110): OSEL=10, no shifts, logical_op=0, CISEL/BSEL=0.
    check_or_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b110) |-> (OSEL == 2'b10) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // For default (111): OSEL=11, no shifts, not logical, CISEL/BSEL=0.
    check_default_111_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OP == 3'b111) |-> (OSEL == 2'b11) && (SHIFT_LA == 1'b0) && (SHIFT_LR == 1'b0) && (LOGICAL_OP == 1'b0) && (CISEL == 1'b0) && (BSEL == 1'b0)
    );

    // Any SHIFT_LA high implies OSEL selects shift path (01).
    check_shift_la_implies_osel01: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (SHIFT_LA == 1'b1) |-> (OSEL == 2'b01)
    );

    // Any SHIFT_LR high implies OSEL selects shift path (01).
    check_shift_lr_implies_osel01: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (SHIFT_LR == 1'b1) |-> (OSEL == 2'b01)
    );

    // LOGICAL_OP high only for AND opcode and implies OSEL==10.
    check_logical_op_implies_and: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (LOGICAL_OP == 1'b1) |-> ((OP == 3'b101) && (OSEL == 2'b10))
    );

endmodule