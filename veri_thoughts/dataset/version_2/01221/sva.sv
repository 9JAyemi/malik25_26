module alu_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);
    // When opcode=000, out is A+B modulo 16.
    check_add_result: assert property (
        @(posedge CLK) (opcode == 3'b000) |-> (out == (A + B)[3:0])
    );

    // When opcode=001, out is A-B modulo 16.
    check_sub_result: assert property (
        @(posedge CLK) (opcode == 3'b001) |-> (out == (A - B)[3:0])
    );

    // When opcode=010, out is A & B.
    check_and_result: assert property (
        @(posedge CLK) (opcode == 3'b010) |-> (out == (A & B))
    );

    // When opcode=011, out is A | B.
    check_or_result: assert property (
        @(posedge CLK) (opcode == 3'b011) |-> (out == (A | B))
    );

    // When opcode=100, out is A ^ B.
    check_xor_result: assert property (
        @(posedge CLK) (opcode == 3'b100) |-> (out == (A ^ B))
    );

    // When opcode=101, out is A shifted left by 1.
    check_sll_result: assert property (
        @(posedge CLK) (opcode == 3'b101) |-> (out == (A << 1))
    );

    // When opcode=110, out is A shifted right by 1.
    check_srl_result: assert property (
        @(posedge CLK) (opcode == 3'b110) |-> (out == (A >> 1))
    );

    // When opcode=111, out is bitwise NOT of A.
    check_not_result: assert property (
        @(posedge CLK) (opcode == 3'b111) |-> (out == (~A))
    );

    // zero flag reflects out==0.
    check_zero_flag_true_when_out_zero: assert property (
        @(posedge CLK) (out == 4'b0000) |-> (zero == 1'b1)
    );

    // zero flag clears when out!=0.
    check_zero_flag_false_when_out_nonzero: assert property (
        @(posedge CLK) (out != 4'b0000) |-> (zero == 1'b0)
    );
endmodule