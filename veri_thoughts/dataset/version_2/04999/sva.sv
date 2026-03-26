module top_module_sva(
    input logic a,
    input logic b,
    input logic out_behavioral,
    input logic out_structural
);

    // Behavioral output must implement XOR.
    check_behavioral_xor: assert property (
        @($global_clock) out_behavioral === (a ^ b)
    );

    // Structural output must implement XOR.
    check_structural_xor: assert property (
        @($global_clock) out_structural === (a ^ b)
    );

    // Both outputs must always match.
    check_outputs_match: assert property (
        @($global_clock) out_behavioral === out_structural
    );

    // Inputs 00 must produce outputs 00.
    check_case_00: assert property (
        @($global_clock) ({a, b} === 2'b00) |-> ({out_behavioral, out_structural} === 2'b00)
    );

    // Inputs 01 must produce outputs 11.
    check_case_01: assert property (
        @($global_clock) ({a, b} === 2'b01) |-> ({out_behavioral, out_structural} === 2'b11)
    );

    // Inputs 10 must produce outputs 11.
    check_case_10: assert property (
        @($global_clock) ({a, b} === 2'b10) |-> ({out_behavioral, out_structural} === 2'b11)
    );

    // Inputs 11 must produce outputs 00.
    check_case_11: assert property (
        @($global_clock) ({a, b} === 2'b11) |-> ({out_behavioral, out_structural} === 2'b00)
    );

endmodule