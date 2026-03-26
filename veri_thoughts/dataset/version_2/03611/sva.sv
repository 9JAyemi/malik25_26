module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset; sample the combinational logic on the formal global clock.

    // Y always matches the logical AND of A1 and A2.
    check_output_matches_and: assert property (
        @($global_clock) Y === (A1 && A2)
    );

    // A low A1 forces Y low.
    check_a1_low_forces_y_low: assert property (
        @($global_clock) (A1 === 1'b0) |-> (Y === 1'b0)
    );

    // A low A2 forces Y low.
    check_a2_low_forces_y_low: assert property (
        @($global_clock) (A2 === 1'b0) |-> (Y === 1'b0)
    );

    // Both high inputs force Y high.
    check_both_high_force_y_high: assert property (
        @($global_clock) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === 1'b1)
    );

    // With A1 and A2 unchanged, Y stays unchanged regardless of other inputs.
    check_y_depends_only_on_a1_a2: assert property (
        @($global_clock) ($stable(A1) && $stable(A2)) |-> $stable(Y)
    );

endmodule