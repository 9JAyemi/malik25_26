module barrel_shifter_alu_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        dir,
    input logic [2:0]  op,
    input logic [3:0]  S
);

    // S must match the full barrel-shifter ALU function.
    check_output_matches_rtl: assert property (
        @(posedge clk) disable iff ($initstate)
        S == (
            (op == 3'b000) ? (A + (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})) :
            (op == 3'b001) ? (A - (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})) :
            (op == 3'b010) ? (A & (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})) :
            (op == 3'b011) ? (A | (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})) :
            (op == 3'b100) ? (A ^ (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})) :
            (op == 3'b101) ? ((dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]}) << 1) :
                             4'b0000
        )
    );

    // op 000 must add A and the shifted A value.
    check_add_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b000) |-> (S == (A + (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})))
    );

    // op 001 must subtract the shifted A value from A.
    check_sub_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b001) |-> (S == (A - (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})))
    );

    // op 010 must bitwise AND A with the shifted A value.
    check_and_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b010) |-> (S == (A & (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})))
    );

    // op 011 must bitwise OR A with the shifted A value.
    check_or_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b011) |-> (S == (A | (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})))
    );

    // op 100 must bitwise XOR A with the shifted A value.
    check_xor_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b100) |-> (S == (A ^ (dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]})))
    );

    // op 101 must left shift the shifted A value once more.
    check_shift_twice_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        (op == 3'b101) |-> (S == ((dir ? {A[2:0], 1'b0} : {1'b0, A[3:1]}) << 1))
    );

    // Unsupported opcodes must drive S to zero.
    check_default_zero_operation: assert property (
        @(posedge clk) disable iff ($initstate)
        ((op == 3'b110) || (op == 3'b111)) |-> (S == 4'b0000)
    );

    // The shift opcode with dir high must produce A shifted left by two.
    check_shift_opcode_left_dir: assert property (
        @(posedge clk) disable iff ($initstate)
        ((op == 3'b101) && dir) |-> (S == {A[1:0], 2'b00})
    );

    // The shift opcode with dir low must produce the RTL right-then-left result.
    check_shift_opcode_right_dir: assert property (
        @(posedge clk) disable iff ($initstate)
        ((op == 3'b101) && !dir) |-> (S == {A[3:1], 1'b0})
    );

    // B is unused, so changing only B must not change S.
    check_b_unused: assert property (
        @(posedge clk) disable iff ($initstate)
        ($changed(B) && $stable(A) && $stable(dir) && $stable(op)) |-> $stable(S)
    );

endmodule