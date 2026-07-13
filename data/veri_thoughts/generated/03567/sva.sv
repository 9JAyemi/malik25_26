module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] OP,
    input logic select,
    input logic [3:0] result,
    input logic eq,
    input logic gt,
    input logic lt
);

    function automatic logic [3:0] add_wrap (
        input logic [3:0] a,
        input logic [3:0] b
    );
        add_wrap = a + b;
    endfunction

    function automatic logic [3:0] sub_wrap (
        input logic [3:0] a,
        input logic [3:0] b
    );
        sub_wrap = a - b;
    endfunction

    // Result is zero when the ALU output is not selected.
    check_result_zero_when_unselected: assert property (
        @(posedge clk) (select === 1'b0) |-> (result === 4'b0000)
    );

    // Addition opcode returns the wrapped 4-bit sum when selected.
    check_result_add: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b000)) |-> (result === add_wrap(A, B))
    );

    // Subtraction opcode returns the wrapped 4-bit difference when selected.
    check_result_sub: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b001)) |-> (result === sub_wrap(A, B))
    );

    // AND opcode returns A & B when selected.
    check_result_and: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b010)) |-> (result === (A & B))
    );

    // OR opcode returns A | B when selected.
    check_result_or: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b011)) |-> (result === (A | B))
    );

    // XOR opcode returns A ^ B when selected.
    check_result_xor: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b100)) |-> (result === (A ^ B))
    );

    // Shift-left opcode returns A shifted left by one when selected.
    check_result_shift_left: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b101)) |-> (result === {A[2:0], 1'b0})
    );

    // Shift-right opcode returns A shifted right by one when selected.
    check_result_shift_right: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b110)) |-> (result === (A >> 1))
    );

    // Invert opcode returns bitwise NOT of A when selected.
    check_result_invert: assert property (
        @(posedge clk) ((select === 1'b1) && (OP === 3'b111)) |-> (result === (~A))
    );

    // eq reflects whether A and B are equal.
    check_eq_flag: assert property (
        @(posedge clk) (eq === (A == B))
    );

    // gt reflects whether A is greater than B.
    check_gt_flag: assert property (
        @(posedge clk) (gt === (A > B))
    );

    // lt reflects whether A is less than B.
    check_lt_flag: assert property (
        @(posedge clk) (lt === (A < B))
    );

endmodule