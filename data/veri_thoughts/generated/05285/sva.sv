module mux_transmission_gate_sva (
    input logic A,
    input logic B,
    input logic SEL,
    input logic OUT
);

    // When SEL is 0, OUT follows A.
    check_sel_low_routes_a: assert property (
        @($global_clock) (SEL === 1'b0) |-> (OUT === A)
    );

    // When SEL is not 0, OUT follows B.
    check_sel_nonzero_routes_b: assert property (
        @($global_clock) (SEL !== 1'b0) |-> (OUT === B)
    );

endmodule