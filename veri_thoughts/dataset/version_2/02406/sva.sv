module alu_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] control,
    input logic [3:0] result
);
    // Analysis: No clock or reset; pure combinational always @(*); result depends only on A,B,control.
    // Function: control=000 add, 001 sub, 010 and, 011 or, default 0000.

    // When control==000, result equals 4-bit A + B.
    check_add_function: assert property (
        @($global_clock) (control == 3'b000) |-> (result == (A + B))
    );

    // When control==001, result equals 4-bit A - B.
    check_sub_function: assert property (
        @($global_clock) (control == 3'b001) |-> (result == (A - B))
    );

    // When control==010, result equals A & B.
    check_and_function: assert property (
        @($global_clock) (control == 3'b010) |-> (result == (A & B))
    );

    // When control==011, result equals A | B.
    check_or_function: assert property (
        @($global_clock) (control == 3'b011) |-> (result == (A | B))
    );

    // For all other control values, result is 0000.
    check_default_zero: assert property (
        @($global_clock) (!(control inside {3'b000,3'b001,3'b010,3'b011})) |-> (result == 4'b0000)
    );

    // If A,B,control are stable, result remains stable (combinational determinism).
    check_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({A,B,control}) |-> $stable(result)
    );

    // Add identity: with B==0, result equals A.
    check_add_zero_identity: assert property (
        @($global_clock) (control == 3'b000 && (B == 4'b0000)) |-> (result == A)
    );

    // Sub identity: with B==0, result equals A.
    check_sub_zero_identity: assert property (
        @($global_clock) (control == 3'b001 && (B == 4'b0000)) |-> (result == A)
    );

    // AND with zero yields zero.
    check_and_zero: assert property (
        @($global_clock) (control == 3'b010 && (B == 4'b0000)) |-> (result == 4'b0000)
    );

    // OR with zero yields A.
    check_or_zero: assert property (
        @($global_clock) (control == 3'b011 && (B == 4'b0000)) |-> (result == A)
    );

    // Subtract/add inverse modulo 16: (A - B) + B == A.
    check_sub_add_inverse_mod16: assert property (
        @($global_clock) (control == 3'b001) |-> ((result + B) == A)
    );

    // AND with ones yields A.
    check_and_ones: assert property (
        @($global_clock) (control == 3'b010 && (B == 4'b1111)) |-> (result == A)
    );

    // OR with ones yields ones.
    check_or_ones: assert property (
        @($global_clock) (control == 3'b011 && (B == 4'b1111)) |-> (result == 4'b1111)
    );

endmodule