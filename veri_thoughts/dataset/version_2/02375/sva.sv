module addsub_4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] O,
    input logic [3:0] A,
    input logic C,
    input logic [3:0] S,
    input logic [3:0] D,
    input logic B
);
    // Addition mode: S is O + A (4-bit).
    check_add_sum: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b1) |-> (S == ((O + A) & 4'hF))
    );

    // Addition mode: D is zero.
    check_add_d_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b1) |-> (D == 4'b0)
    );

    // Addition mode: B is zero.
    check_add_b_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b1) |-> (B == 1'b0)
    );

    // Subtraction mode: S is zero.
    check_sub_s_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0) |-> (S == 4'b0)
    );

    // Subtraction no-borrow path: D = (O - A) (4-bit).
    check_sub_no_borrow_d: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0 && !(O < A)) |-> (D == ((O - A) & 4'hF))
    );

    // Subtraction no-borrow path: B = 0.
    check_sub_no_borrow_b: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0 && !(O < A)) |-> (B == 1'b0)
    );

    // Subtraction borrow path: D = (O + 16) - A (low 4 bits).
    check_sub_borrow_d: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0 && (O < A)) |-> (D == (((O + 5'd16) - A) & 4'hF))
    );

    // Subtraction borrow path: B = 1.
    check_sub_borrow_b: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0 && (O < A)) |-> (B == 1'b1)
    );

    // In subtraction mode, B matches (O < A).
    check_sub_b_matches_comparison: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0) |-> (B == (O < A))
    );

    // In subtraction mode, D equals (O - A) modulo 16.
    check_sub_d_modulo: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0) |-> (D == ((O - A) & 4'hF))
    );

    // Special case: O == A in subtraction yields D=0 and B=0.
    check_sub_equal_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (C == 1'b0 && (O == A)) |-> (D == 4'b0 && B == 1'b0)
    );
endmodule