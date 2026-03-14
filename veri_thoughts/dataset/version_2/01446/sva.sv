module Modulo_sva #(
    parameter int n = 8
) (
    input logic CLK,
    input logic RESETn,
    input logic [n-1:0] numerator,
    input logic [n-1:0] denominator,
    input logic [n-1:0] remainder
);

    // When denominator is zero, remainder must be zero.
    check_zero_denominator_drives_zero_remainder: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator == {n{1'b0}}) |-> (remainder == {n{1'b0}})
    );

    // When denominator is nonzero and numerator < denominator, remainder equals numerator.
    check_lt_path_returns_numerator: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator != {n{1'b0}} && (numerator < denominator)) |-> (remainder == numerator)
    );

    // When denominator is nonzero and numerator == denominator, remainder is zero.
    check_equal_values_return_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator != {n{1'b0}} && (numerator == denominator)) |-> (remainder == {n{1'b0}})
    );

    // For nonzero denominator, remainder is strictly less than denominator.
    check_remainder_less_than_denominator_when_div_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator != {n{1'b0}}) |-> (remainder < denominator)
    );

    // Remainder is never greater than numerator.
    check_remainder_not_greater_than_numerator: assert property (
        @(posedge CLK) disable iff (!RESETn) (remainder <= numerator)
    );

    // For nonzero denominator, remainder equals numerator % denominator.
    check_mod_equivalence_when_div_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator != {n{1'b0}}) |-> (remainder == (numerator % denominator))
    );

    // For nonzero denominator, remainder equals numerator - (floor(numerator/denominator) * denominator).
    check_division_identity_when_div_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator != {n{1'b0}}) |-> 
            (remainder == (numerator - (((numerator / denominator) * denominator)[n-1:0])))
    );

    // When denominator is one, remainder must be zero.
    check_denominator_one_gives_zero_remainder: assert property (
        @(posedge CLK) disable iff (!RESETn) (denominator == {{(n-1){1'b0}},1'b1}) |-> (remainder == {n{1'b0}})
    );

    // When numerator is zero, remainder must be zero.
    check_zero_numerator_gives_zero_remainder: assert property (
        @(posedge CLK) disable iff (!RESETn) (numerator == {n{1'b0}}) |-> (remainder == {n{1'b0}})
    );

    // If inputs are stable cycle-to-cycle, remainder is stable (purely combinational behavior).
    check_stable_io_yields_stable_remainder: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(numerator) && $stable(denominator)) |-> $stable(remainder)
    );

endmodule