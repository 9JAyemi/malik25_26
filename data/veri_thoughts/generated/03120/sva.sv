module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND
);

    // Combinational RTL with no explicit clock or reset; sample on the formal global clock.

    // Y matches the implemented RTL function ~A1 | ~A2 | ~B1.
    check_y_matches_rtl_function: assert property (
        @($global_clock) Y == ((~A1) | (~A2) | (~B1))
    );

    // All three inputs high drive Y low.
    check_all_inputs_high_drive_y_low: assert property (
        @($global_clock) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low A1 forces Y high.
    check_a1_low_drives_y_high: assert property (
        @($global_clock) (A1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low A2 forces Y high.
    check_a2_low_drives_y_high: assert property (
        @($global_clock) (A2 == 1'b0) |-> (Y == 1'b1)
    );

    // A low B1 forces Y high.
    check_b1_low_drives_y_high: assert property (
        @($global_clock) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low Y implies all three inputs are high.
    check_y_low_implies_all_inputs_high: assert property (
        @($global_clock) (Y == 1'b0) |-> ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1))
    );

endmodule