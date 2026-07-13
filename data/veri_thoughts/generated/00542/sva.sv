module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal B1 OR the three-input AND of A1, A2, and A3.
    check_output_function: assert property (
        @($global_clock) X == (B1 | (A1 & A2 & A3))
    );

    // A high B1 must drive the OR output high.
    check_b1_forces_output_high: assert property (
        @($global_clock) B1 |-> X
    );

    // All three A inputs high must drive X high through the AND path.
    check_and_path_forces_output_high: assert property (
        @($global_clock) (A1 & A2 & A3) |-> X
    );

    // When both OR inputs are low, X must be low.
    check_output_low_when_or_inputs_low: assert property (
        @($global_clock) (!B1 && !(A1 & A2 & A3)) |-> !X
    );

endmodule