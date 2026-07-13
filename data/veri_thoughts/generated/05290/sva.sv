module sky130_fd_sc_hd__nor2_sva (
    input logic Y,
    input logic A,
    input logic B
);

    // No RTL clock or reset; sample on the formal global clock.
    // The DUT is pure combinational logic implementing Y = ~(A | B).

    // Y must equal the NOR of A and B.
    check_nor_function: assert property (
        @($global_clock) (Y === ~(A | B))
    );

    // A high forces Y low.
    check_a_high_forces_y_low: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high forces Y low.
    check_b_high_forces_y_low: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // Both inputs low force Y high.
    check_inputs_low_drive_y_high: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // Y high means both inputs are low.
    check_y_high_implies_inputs_low: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

    // Y low means at least one input is high.
    check_y_low_implies_some_input_high: assert property (
        @($global_clock) (Y === 1'b0) |-> ((A === 1'b1) || (B === 1'b1))
    );

endmodule