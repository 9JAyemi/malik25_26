module full_adder_en_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic En,
    input logic Sum,
    input logic Cout
);

    // Combinational DUT with no explicit clock or reset; use the formal global clock.

    // When disabled, both outputs are forced low.
    check_disabled_outputs_zero: assert property (
        @($global_clock)
        (En == 1'b0) |-> (Sum == 1'b0 && Cout == 1'b0)
    );

    // When enabled, Sum matches the three-input XOR function.
    check_enabled_sum_function: assert property (
        @($global_clock)
        (En == 1'b1) |-> (Sum == (A ^ B ^ Cin))
    );

    // When enabled, Cout matches the RTL carry equation.
    check_enabled_carry_function: assert property (
        @($global_clock)
        (En == 1'b1) |-> (Cout == ((A & B) | (Cin & (A ^ B))))
    );

    // When enabled, the outputs equal the 2-bit sum of A, B, and Cin.
    check_enabled_full_adder_result: assert property (
        @($global_clock)
        (En == 1'b1) |-> ({Cout, Sum} == ({1'b0, A} + {1'b0, B} + {1'b0, Cin}))
    );

endmodule