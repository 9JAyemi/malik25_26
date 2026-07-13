module comb_circuit_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // When a and b are both high, out is the inverse of c.
    check_case_11_inverts_c: assert property (
        @($global_clock) disable iff (1'b0) ({a, b} == 2'b11) |-> (out == ~c)
    );

    // When a is high and b is low, out matches c.
    check_case_10_passes_c: assert property (
        @($global_clock) disable iff (1'b0) ({a, b} == 2'b10) |-> (out == c)
    );

    // When a is low and b is high, out is the inverse of c.
    check_case_01_inverts_c: assert property (
        @($global_clock) disable iff (1'b0) ({a, b} == 2'b01) |-> (out == ~c)
    );

    // When a and b are both low, out is forced low.
    check_case_00_forces_low: assert property (
        @($global_clock) disable iff (1'b0) ({a, b} == 2'b00) |-> (out == 1'b0)
    );

    // Out always matches the full combinational case expression.
    check_full_function_equation: assert property (
        @($global_clock) disable iff (1'b0) out == (b ? ~c : (a ? c : 1'b0))
    );

endmodule