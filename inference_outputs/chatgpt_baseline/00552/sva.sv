module karnaugh_map_sva(
    input logic A,
    input logic B,
    input logic C,
    input logic F
);

    // F simplifies to A for all known input combinations.
    check_function_reduces_to_a: assert property (
        @($global_clock) !$isunknown({A,B,C}) |-> (F === A)
    );

    // For input 000, the selected minterm evaluates to 0.
    check_case_000_output_zero: assert property (
        @($global_clock) ({A,B,C} === 3'b000) |-> (F === 1'b0)
    );

    // For input 001, the selected minterm evaluates to 0.
    check_case_001_output_zero: assert property (
        @($global_clock) ({A,B,C} === 3'b001) |-> (F === 1'b0)
    );

    // For input 010, the selected minterm evaluates to 0.
    check_case_010_output_zero: assert property (
        @($global_clock) ({A,B,C} === 3'b010) |-> (F === 1'b0)
    );

    // For input 011, the selected minterm evaluates to 0.
    check_case_011_output_zero: assert property (
        @($global_clock) ({A,B,C} === 3'b011) |-> (F === 1'b0)
    );

    // For input 100, the selected minterm evaluates to 1.
    check_case_100_output_one: assert property (
        @($global_clock) ({A,B,C} === 3'b100) |-> (F === 1'b1)
    );

    // For input 101, the selected minterm evaluates to 1.
    check_case_101_output_one: assert property (
        @($global_clock) ({A,B,C} === 3'b101) |-> (F === 1'b1)
    );

    // For input 110, the selected minterm evaluates to 1.
    check_case_110_output_one: assert property (
        @($global_clock) ({A,B,C} === 3'b110) |-> (F === 1'b1)
    );

    // For input 111, the selected minterm evaluates to 1.
    check_case_111_output_one: assert property (
        @($global_clock) ({A,B,C} === 3'b111) |-> (F === 1'b1)
    );

endmodule