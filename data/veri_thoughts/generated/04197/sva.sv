module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X
);

    // Combinational DUT with no explicit clock or reset; sample on $global_clock.
    // A1/A2 feed the AND path, A3/A4 feed the OR path, and B1 selects X.

    // X must match the full muxed Boolean function.
    check_output_function: assert property (
        @($global_clock) disable iff (1'b0)
        X == (B1 ? (A1 & A2) : (A3 | A4))
    );

    // When B1 is high, X must equal A1 AND A2.
    check_select_and_path: assert property (
        @($global_clock) disable iff (1'b0)
        B1 |-> (X == (A1 & A2))
    );

    // When B1 is low, X must equal A3 OR A4.
    check_select_or_path: assert property (
        @($global_clock) disable iff (1'b0)
        !B1 |-> (X == (A3 | A4))
    );

    // Selecting the AND path with both inputs high drives X high.
    check_and_path_high: assert property (
        @($global_clock) disable iff (1'b0)
        (B1 && A1 && A2) |-> (X == 1'b1)
    );

    // Selecting the AND path with either input low drives X low.
    check_and_path_low: assert property (
        @($global_clock) disable iff (1'b0)
        (B1 && (!A1 || !A2)) |-> (X == 1'b0)
    );

    // Selecting the OR path with any input high drives X high.
    check_or_path_high: assert property (
        @($global_clock) disable iff (1'b0)
        (!B1 && (A3 || A4)) |-> (X == 1'b1)
    );

    // Selecting the OR path with both inputs low drives X low.
    check_or_path_low: assert property (
        @($global_clock) disable iff (1'b0)
        (!B1 && !A3 && !A4) |-> (X == 1'b0)
    );

endmodule