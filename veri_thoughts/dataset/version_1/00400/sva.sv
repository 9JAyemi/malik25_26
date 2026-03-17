module adder_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic enable,
    input logic [7:0] C
);

    // C always matches the combinational add-or-zero function.
    check_functional_relation: assert property (
        @($global_clock) C == (enable ? (A + B) : 8'h00)
    );

    // When enable is high, C equals the 8-bit sum of A and B.
    check_enabled_add: assert property (
        @($global_clock) enable |-> (C == (A + B))
    );

    // When enable is low, C is driven to zero.
    check_disabled_zero: assert property (
        @($global_clock) !enable |-> (C == 8'h00)
    );

    // With stable inputs, the combinational output remains stable.
    check_stable_inputs_stable_output: assert property (
        @($global_clock) $stable({A, B, enable}) |-> $stable(C)
    );

endmodule