module MUXCY_sva (
    input logic clk,
    input logic O,
    input logic CO,
    input logic CI,
    input logic DI,
    input logic S,
    input logic CIN
);

    // O matches the implemented sum equation.
    check_sum_equation: assert property (
        @(posedge clk) O == ((S & DI) | (~S & CI))
    );

    // CO matches the implemented carry equation.
    check_carry_equation: assert property (
        @(posedge clk) CO == (((CI & S) | (DI & (CI | S))) & CIN)
    );

    // With CIN low, both outputs are low.
    check_cin_low_forces_outputs_low: assert property (
        @(posedge clk) !CIN |-> (!O && !CO)
    );

    // With CIN high, CO reduces to the implemented carry term.
    check_cin_high_reduces_carry: assert property (
        @(posedge clk) CIN |-> (CO == ((CI & S) | (DI & (CI | S))))
    );

    // With S low, O follows CI and CO reduces to DI gated by CI.
    check_select_low_behavior: assert property (
        @(posedge clk) !S |-> (O == CI && CO == (DI & CI))
    );

    // With S high, O follows DI and CO reduces to CI gated by DI.
    check_select_high_behavior: assert property (
        @(posedge clk) S |-> (O == DI && CO == (CI & DI))
    );

    // With S low and DI low, both outputs are low.
    check_select_low_di_low: assert property (
        @(posedge clk) (!S && !DI) |-> (!O && !CO)
    );

    // With S low and DI high, both outputs follow CI.
    check_select_low_di_high: assert property (
        @(posedge clk) (!S && DI) |-> (O == CI && CO == CI)
    );

    // With S high and CI low, both outputs are low.
    check_select_high_ci_low: assert property (
        @(posedge clk) (S && !CI) |-> (!O && !CO)
    );

    // With S high and CI high, both outputs follow DI.
    check_select_high_ci_high: assert property (
        @(posedge clk) (S && CI) |-> (O == DI && CO == DI)
    );

endmodule