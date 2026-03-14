module adder_subtractor_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       mode,
    input logic [7:0] result
);
    ///// Combinational arithmetic rules (clocked on $global_clock) /////

    // Result matches A + (mode ? (~B + 1) : B).
    check_result_definition: assert property (
        @(posedge $global_clock) result == (A + (mode ? ((~B) + 8'h01) : B))
    );

    // In add mode (mode=0), result equals A + B.
    check_mode0_add: assert property (
        @(posedge $global_clock) (!mode) |-> (result == (A + B))
    );

    // In subtract mode (mode=1), result equals A + (~B + 1).
    check_mode1_sub: assert property (
        @(posedge $global_clock) (mode) |-> (result == (A + ((~B) + 8'h01)))
    );

    // If B is zero, result passes A regardless of mode.
    check_b_zero_passthrough: assert property (
        @(posedge $global_clock) (B == 8'h00) |-> (result == A)
    );

    // If A is zero in add mode, result passes B.
    check_a_zero_mode0_passthrough: assert property (
        @(posedge $global_clock) (!mode && (A == 8'h00)) |-> (result == B)
    );

    // If A equals B in subtract mode, result is zero.
    check_a_eq_b_mode1_zero: assert property (
        @(posedge $global_clock) (mode && (A == B)) |-> (result == 8'h00)
    );

    // In subtract mode, adding B back to result yields A (mod 256).
    check_inverse_mode1_add_back_b: assert property (
        @(posedge $global_clock) mode |-> ((result + B) == A)
    );

    // In add mode, subtracting B from result yields A (mod 256).
    check_inverse_mode0_subtract_b: assert property (
        @(posedge $global_clock) (!mode) |-> ((result + ((~B) + 8'h01)) == A)
    );

    // In add mode, subtracting A from result yields B (mod 256).
    check_inverse_mode0_subtract_a: assert property (
        @(posedge $global_clock) (!mode) |-> ((result + ((~A) + 8'h01)) == B)
    );

    // If A, B, and mode are stable across cycles, result is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge $global_clock) ($stable(A) && $stable(B) && $stable(mode)) |-> $stable(result)
    );

endmodule