module alu_assertions (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [2:0]  OP,
    input logic [3:0]  Y
);

    // Addition opcode drives Y to A + B.
    check_add_result: assert property (
        @(posedge clk) (OP === 3'b000) |-> (Y == (A + B))
    );

    // Subtraction opcode drives Y to A - B.
    check_sub_result: assert property (
        @(posedge clk) (OP === 3'b001) |-> (Y == (A - B))
    );

    // AND opcode drives Y to A & B.
    check_and_result: assert property (
        @(posedge clk) (OP === 3'b010) |-> (Y == (A & B))
    );

    // OR opcode drives Y to A | B.
    check_or_result: assert property (
        @(posedge clk) (OP === 3'b011) |-> (Y == (A | B))
    );

    // XOR opcode drives Y to A ^ B.
    check_xor_result: assert property (
        @(posedge clk) (OP === 3'b100) |-> (Y == (A ^ B))
    );

endmodule