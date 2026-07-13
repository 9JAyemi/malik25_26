module simple_logic_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic Y
);
    // Output is always the bitwise inverse of input.
    check_inversion: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y === ~A)
    );

    // If A is stable this cycle, Y must also be stable.
    check_stability_propagation: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(A) |-> $stable(Y)
    );

    // If Y changes between cycles, A must have changed.
    check_change_dependency: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> $changed(A)
    );

    // A rising edge implies Y falls (due to inversion).
    check_edge_rise: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies Y rises (due to inversion).
    check_edge_fall: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(A) |-> $rose(Y)
    );
endmodule