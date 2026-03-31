module addsub_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        C,
    input logic [15:0] Q
);

// When C is high, Q must be A minus B.
    check_subtract_result: assert property (
        @(posedge clk) (C == 1'b1) |-> (Q == (A - B))
    );

// When C is low, Q must be A plus B.
    check_add_result: assert property (
        @(posedge clk) (C == 1'b0) |-> (Q == (A + B))
    );

// Zero on B must pass A through unchanged regardless of C.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 16'h0000) |-> (Q == A)
    );

// Zero on A must pass B through unchanged regardless of C.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 16'h0000) |-> (Q == B)
    );

// Equal operands must produce zero regardless of C.
    check_equal_operands_zero: assert property (
        @(posedge clk) (A == B) |-> (Q == 16'h0000)
    );

// Subtracting equal operands must produce zero.
    check_subtract_equal_operands_zero: assert property (
        @(posedge clk) (C == 1'b1) && (A == B) |-> (Q == 16'h0000)
    );

// Adding equal operands must produce double that value.
    check_add_equal_operands_double: assert property (
        @(posedge clk) (C == 1'b0) && (A == B) |-> (Q == (A << 1))
    );

endmodule
