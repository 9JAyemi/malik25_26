module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic Sum,
    input logic Cout
);

    // Sum is the xor of all three inputs.
    check_sum_definition: assert property (
        @(posedge clk) Sum == (A ^ B ^ Cin)
    );

    // Cout matches the implemented carry equation.
    check_cout_definition: assert property (
        @(posedge clk) Cout == ((A & B) | (Cin & (A ^ B)))
    );

    // 000 produces no sum bit and no carry.
    check_add_000: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && Cin == 1'b0) |-> ({Cout, Sum} == 2'b00)
    );

    // 001 produces sum 1 with no carry.
    check_add_001: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && Cin == 1'b1) |-> ({Cout, Sum} == 2'b01)
    );

    // 010 produces sum 1 with no carry.
    check_add_010: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1 && Cin == 1'b0) |-> ({Cout, Sum} == 2'b01)
    );

    // 011 produces carry 1 and sum 0.
    check_add_011: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1 && Cin == 1'b1) |-> ({Cout, Sum} == 2'b10)
    );

    // 100 produces sum 1 with no carry.
    check_add_100: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0 && Cin == 1'b0) |-> ({Cout, Sum} == 2'b01)
    );

    // 101 produces carry 1 and sum 0.
    check_add_101: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0 && Cin == 1'b1) |-> ({Cout, Sum} == 2'b10)
    );

    // 110 produces carry 1 and sum 0.
    check_add_110: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1 && Cin == 1'b0) |-> ({Cout, Sum} == 2'b10)
    );

    // 111 produces sum 1 and carry 1.
    check_add_111: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1 && Cin == 1'b1) |-> ({Cout, Sum} == 2'b11)
    );

endmodule