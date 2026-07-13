module MUXCY_sva (
    input logic clk,
    input logic O,
    input logic CO,
    input logic CI,
    input logic DI,
    input logic S,
    input logic CIN
);

    // O matches the RTL mux equation.
    check_o_equation: assert property (
        @(posedge clk) O == ((S & DI) | (~S & CI))
    );

    // CO matches the RTL carry equation.
    check_co_equation: assert property (
        @(posedge clk) CO == ((CI & S) | (DI & (CI | S)))
    );

    // When S is high, O selects DI.
    check_o_selects_di_when_s_high: assert property (
        @(posedge clk) S |-> (O == DI)
    );

    // When S is low, O selects CI.
    check_o_selects_ci_when_s_low: assert property (
        @(posedge clk) !S |-> (O == CI)
    );

    // When S is high, CO reduces to CI OR DI.
    check_co_reduces_to_or_when_s_high: assert property (
        @(posedge clk) S |-> (CO == (CI | DI))
    );

    // When S is low, CO reduces to CI AND DI.
    check_co_reduces_to_and_when_s_low: assert property (
        @(posedge clk) !S |-> (CO == (CI & DI))
    );

    // Stable functional inputs imply stable outputs.
    check_outputs_stable_when_functional_inputs_stable: assert property (
        @(posedge clk) $stable({CI, DI, S}) |-> $stable({O, CO})
    );

    // CIN is unused and cannot change O or CO by itself.
    check_outputs_ignore_cin_changes: assert property (
        @(posedge clk) ($changed(CIN) && $stable({CI, DI, S})) |-> $stable({O, CO})
    );

    // Equal data inputs force both outputs to that shared value.
    check_equal_inputs_drive_equal_outputs: assert property (
        @(posedge clk) (CI == DI) |-> ((O == CI) && (CO == CI))
    );

endmodule