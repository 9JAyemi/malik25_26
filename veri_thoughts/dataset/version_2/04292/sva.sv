module mux_2to1_assertions (
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // The RTL has no clock or reset, so assertions use the formal global clock.

    // Output always matches the implemented mux function.
    check_mux_function: assert property (
        @($global_clock)
        Y === ((S === 1'b0) ? A : ((S === 1'b1) ? B : 1'b0))
    );

    // Select low routes input A to the output.
    check_select_low_routes_a: assert property (
        @($global_clock)
        (S === 1'b0) |-> (Y === A)
    );

    // Select high routes input B to the output.
    check_select_high_routes_b: assert property (
        @($global_clock)
        (S === 1'b1) |-> (Y === B)
    );

    // A non-binary select value drives the default zero output.
    check_invalid_select_drives_zero: assert property (
        @($global_clock)
        ((S !== 1'b0) && (S !== 1'b1)) |-> (Y === 1'b0)
    );

    // Changes on B do not affect Y when A is selected and stable.
    check_b_ignored_when_select_low: assert property (
        @($global_clock)
        ($stable(S) && (S === 1'b0) && $stable(A) && $changed(B)) |-> $stable(Y)
    );

    // Changes on A do not affect Y when B is selected and stable.
    check_a_ignored_when_select_high: assert property (
        @($global_clock)
        ($stable(S) && (S === 1'b1) && $stable(B) && $changed(A)) |-> $stable(Y)
    );

endmodule