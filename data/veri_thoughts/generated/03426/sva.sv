module mux_2_1_sva (
    input logic in_0,
    input logic in_1,
    input logic sel,
    input logic out
);

    // sel==0 selects in_0.
    check_sel_zero_routes_in0: assert property (
        @($global_clock) (sel === 1'b0) |-> (out === in_0)
    );

    // Any sel value other than 0 takes the else branch and selects in_1.
    check_sel_nonzero_routes_in1: assert property (
        @($global_clock) (sel !== 1'b0) |-> (out === in_1)
    );

endmodule