module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic clk
);

    // External clk samples this combinational DUT.

    // Y matches the implemented AND/NOT/OR/NOR function.
    check_full_boolean_function: assert property (
        @(posedge clk)
        Y == ~((A1 & A2) | ((~B1) | C1))
    );

    // B1 low forces the OR path high and Y low.
    check_b1_low_forces_y_low: assert property (
        @(posedge clk)
        !B1 |-> !Y
    );

    // C1 high forces the OR path high and Y low.
    check_c1_high_forces_y_low: assert property (
        @(posedge clk)
        C1 |-> !Y
    );

    // A1 and A2 high force the NOR output low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk)
        (A1 && A2) |-> !Y
    );

    // Y high requires B1 high, C1 low, and at least one A input low.
    check_y_high_requires_enable_terms: assert property (
        @(posedge clk)
        Y |-> (B1 && !C1 && (!A1 || !A2))
    );

    // B1 high, C1 low, and either A input low force Y high.
    check_enable_terms_force_y_high: assert property (
        @(posedge clk)
        (B1 && !C1 && (!A1 || !A2)) |-> Y
    );

    // Y low means at least one blocking term is active.
    check_y_low_requires_blocking_term: assert property (
        @(posedge clk)
        !Y |-> ((A1 && A2) || !B1 || C1)
    );

endmodule