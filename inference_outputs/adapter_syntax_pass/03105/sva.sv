module bitwise_op_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // sel=00 drives out to A & B.
    check_and_select: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == (A & B))
    );

    // sel=01 drives out to A | B.
    check_or_select: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == (A | B))
    );

    // sel=10 drives out to A ^ B.
    check_xor_select: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == (A ^ B))
    );

    // sel=11 drives out to ~(A ^ B).
    check_nxor_select: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == ~(A ^ B))
    );

    // sel values other than 00/01/10/11 drive out to zero.
    check_default_zero: assert property (
        @($global_clock) ((sel != 2'b00) && (sel != 2'b01) && (sel != 2'b10) && (sel != 2'b11)) |-> (out == 4'b0000)
    );

endmodule