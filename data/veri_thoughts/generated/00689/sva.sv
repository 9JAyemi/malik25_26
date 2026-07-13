module ALU_sva #(parameter N=32) (
    input logic [3:0] op_code,
    input logic signed [N-1:0] operand1,
    input logic signed [N-1:0] operand2,
    input logic clk,
    input logic signed [N-1:0] result,
    input logic zero,
    input logic overflow
);

    // SLL: result/zero/overflow per shift-left logical
    check_sll_behavior: assert property (
        @(posedge clk) (op_code == 4'd0) |-> ##0
            ( (result == (operand2 << operand1[4:0])) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // SRL: result/zero/overflow per shift-right logical
    check_srl_behavior: assert property (
        @(posedge clk) (op_code == 4'd1) |-> ##0
            ( (result == (operand2 >> operand1[4:0])) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // SRA: result/zero/overflow per shift-right arithmetic
    check_sra_behavior: assert property (
        @(posedge clk) (op_code == 4'd2) |-> ##0
            ( (result == (operand2 >>> operand1[4:0])) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // ADD: result equals sum; zero flag; overflow per RTL formula
    check_add_behavior: assert property (
        @(posedge clk) (op_code == 4'd3) |-> ##0
            ( (result == (operand1 + operand2)) &&
              (zero == (result == 0)) &&
              (overflow == ((result[N-1] != operand1[N-1]) && (result[N-1] != operand2[N-1]))) )
    );

    // SUB: result equals difference; zero flag; overflow per RTL formula
    check_sub_behavior: assert property (
        @(posedge clk) (op_code == 4'd4) |-> ##0
            ( (result == (operand1 - operand2)) &&
              (zero == (result == 0)) &&
              (overflow == ((result[N-1] != operand1[N-1]) && (result[N-1] == operand2[N-1]))) )
    );

    // AND: bitwise and; zero flag; overflow must be 0
    check_and_behavior: assert property (
        @(posedge clk) (op_code == 4'd5) |-> ##0
            ( (result == (operand1 & operand2)) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // OR: bitwise or; zero flag; overflow must be 0
    check_or_behavior: assert property (
        @(posedge clk) (op_code == 4'd6) |-> ##0
            ( (result == (operand1 | operand2)) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // XOR: bitwise xor; zero flag; overflow must be 0
    check_xor_behavior: assert property (
        @(posedge clk) (op_code == 4'd7) |-> ##0
            ( (result == (operand1 ^ operand2)) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // NOR: bitwise nor; zero flag; overflow must be 0
    check_nor_behavior: assert property (
        @(posedge clk) (op_code == 4'd8) |-> ##0
            ( (result == ~(operand1 | operand2)) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // SLT: result is (operand1 < operand2); zero flag; overflow must be 0
    check_slt_behavior: assert property (
        @(posedge clk) (op_code == 4'd9) |-> ##0
            ( (result == (operand1 < operand2)) &&
              (zero == (result == 0)) &&
              (overflow == 1'b0) )
    );

    // Default: for undefined opcodes, outputs are all zero
    check_default_behavior: assert property (
        @(posedge clk) (!(op_code inside {4'd0,4'd1,4'd2,4'd3,4'd4,4'd5,4'd6,4'd7,4'd8,4'd9})) |-> ##0
            ( (result == 0) && (zero == 1'b0) && (overflow == 1'b0) )
    );

endmodule