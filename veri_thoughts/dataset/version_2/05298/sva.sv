module Adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // No explicit clock or reset; sample this combinational RTL on $global_clock.

    // Sum matches the RTL XOR equation.
    check_sum_equation: assert property (
        @($global_clock) Sum == ((A ^ B) ^ {4{Cin}})
    );

    // Cout matches bit 0 of the RTL carry expression.
    check_cout_equation: assert property (
        @($global_clock)
        Cout == ((A[0] & B[0]) | ((((A[0] ^ B[0]) ^ Cin) & (A[0] ^ B[0]))))
    );

    // With Cin low, Sum is just A XOR B.
    check_sum_when_cin_low: assert property (
        @($global_clock) (Cin == 1'b0) |-> (Sum == (A ^ B))
    );

    // With Cin high, Sum is the inverse of A XOR B.
    check_sum_when_cin_high: assert property (
        @($global_clock) (Cin == 1'b1) |-> (Sum == ~(A ^ B))
    );

    // Equal inputs with Cin low produce a zero Sum.
    check_sum_zero_when_inputs_equal_and_cin_low: assert property (
        @($global_clock) ((A == B) && (Cin == 1'b0)) |-> (Sum == 4'b0000)
    );

    // Equal inputs with Cin high produce an all-ones Sum.
    check_sum_ones_when_inputs_equal_and_cin_high: assert property (
        @($global_clock) ((A == B) && (Cin == 1'b1)) |-> (Sum == 4'b1111)
    );

    // LSB generate forces Cout high.
    check_cout_generate_lsb: assert property (
        @($global_clock) (A[0] & B[0]) |-> (Cout == 1'b1)
    );

    // LSB both zero forces Cout low.
    check_cout_zero_lsb: assert property (
        @($global_clock) (~A[0] & ~B[0]) |-> (Cout == 1'b0)
    );

    // LSB mismatch makes Cout the inverse of Cin.
    check_cout_inverted_cin_on_lsb_mismatch: assert property (
        @($global_clock) (A[0] ^ B[0]) |-> (Cout == ~Cin)
    );

endmodule