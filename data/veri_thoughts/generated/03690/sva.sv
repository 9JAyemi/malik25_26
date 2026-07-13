module top_module_assertions (
    input logic [15:0] in,
    input logic [3:0]  sel,
    input logic        EN,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [2:0]  op,
    input logic [3:0]  out,
    input logic        valid
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // valid is low only for opcode 3'b101.
    check_valid_decode: assert property (
        @($global_clock) (valid == (op != 3'b101))
    );

    // ADD opcode drives the ALU sum to out and keeps valid high.
    check_add_out: assert property (
        @($global_clock) (op == 3'b000) |-> ((valid == 1'b1) && (out == (A + B)))
    );

    // SUB opcode drives the ALU difference to out and keeps valid high.
    check_sub_out: assert property (
        @($global_clock) (op == 3'b001) |-> ((valid == 1'b1) && (out == (A - B)))
    );

    // AND opcode drives the bitwise AND to out and keeps valid high.
    check_and_out: assert property (
        @($global_clock) (op == 3'b010) |-> ((valid == 1'b1) && (out == (A & B)))
    );

    // OR opcode drives the bitwise OR to out and keeps valid high.
    check_or_out: assert property (
        @($global_clock) (op == 3'b011) |-> ((valid == 1'b1) && (out == (A | B)))
    );

    // XOR opcode drives the bitwise XOR to out and keeps valid high.
    check_xor_out: assert property (
        @($global_clock) (op == 3'b100) |-> ((valid == 1'b1) && (out == (A ^ B)))
    );

    // Unhandled ALU opcodes 110 and 111 drive zero while valid stays high.
    check_default_alu_out: assert property (
        @($global_clock) ((op == 3'b110) || (op == 3'b111)) |-> ((valid == 1'b1) && (out == 4'b0000))
    );

    // Opcode 101 with EN low drives zero and deasserts valid.
    check_invalid_op_en_low_zero: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b0)) |-> ((valid == 1'b0) && (out == 4'b0000))
    );

    // Opcode 101 with EN high and sel 0 forwards in[3:0].
    check_mux_sel0: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b1) && (sel == 4'd0)) |-> ((valid == 1'b0) && (out == in[3:0]))
    );

    // Opcode 101 with EN high and sel 1 forwards in[7:4].
    check_mux_sel1: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b1) && (sel == 4'd1)) |-> ((valid == 1'b0) && (out == in[7:4]))
    );

    // Opcode 101 with EN high and sel 2 forwards in[11:8].
    check_mux_sel2: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b1) && (sel == 4'd2)) |-> ((valid == 1'b0) && (out == in[11:8]))
    );

    // Opcode 101 with EN high and sel 3 forwards in[15:12].
    check_mux_sel3: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b1) && (sel == 4'd3)) |-> ((valid == 1'b0) && (out == in[15:12]))
    );

    // Opcode 101 with EN high and unmapped sel values drives zero.
    check_mux_default_zero: assert property (
        @($global_clock) ((op == 3'b101) && (EN == 1'b1) && (sel > 4'd3)) |-> ((valid == 1'b0) && (out == 4'b0000))
    );

endmodule