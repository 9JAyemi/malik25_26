module alu_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

// Add opcode drives out to A + B.
    check_add_result: assert property (
        @(posedge clk) (opcode == 3'b000) |-> (out == (A + B))
    );

// Subtract opcode drives out to A - B.
    check_sub_result: assert property (
        @(posedge clk) (opcode == 3'b001) |-> (out == (A - B))
    );

// AND opcode drives out to A & B.
    check_and_result: assert property (
        @(posedge clk) (opcode == 3'b010) |-> (out == (A & B))
    );

// OR opcode drives out to A | B.
    check_or_result: assert property (
        @(posedge clk) (opcode == 3'b011) |-> (out == (A | B))
    );

// XOR opcode drives out to A ^ B.
    check_xor_result: assert property (
        @(posedge clk) (opcode == 3'b100) |-> (out == (A ^ B))
    );

// Shift-left opcode drives out to A << 1.
    check_shift_left_result: assert property (
        @(posedge clk) (opcode == 3'b101) |-> (out == (A << 1))
    );

// Shift-right opcode drives out to A >> 1.
    check_shift_right_result: assert property (
        @(posedge clk) (opcode == 3'b110) |-> (out == (A >> 1))
    );

// NOT opcode drives out to ~A.
    check_not_result: assert property (
        @(posedge clk) (opcode == 3'b111) |-> (out == (~A))
    );

// Zero flag is asserted when out is zero.
    check_zero_flag_set: assert property (
        @(posedge clk) (out == 4'b0000) |-> (zero == 1'b1)
    );

// Zero flag is deasserted when out is non-zero.
    check_zero_flag_clear: assert property (
        @(posedge clk) (out != 4'b0000) |-> (zero == 1'b0)
    );

endmodule
