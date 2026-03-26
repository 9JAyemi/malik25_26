module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must always equal the NAND of A1, A2, and A3.
    check_nand_function: assert property (
        @($global_clock) X == ~(A1 & A2 & A3)
    );

    // All three functional inputs high must drive X low.
    check_all_high_drives_low: assert property (
        @($global_clock) (A1 & A2 & A3) |-> (X == 1'b0)
    );

    // Any low on the functional inputs must drive X high.
    check_any_low_drives_high: assert property (
        @($global_clock) !(A1 & A2 & A3) |-> (X == 1'b1)
    );

    // Changes on unused inputs must not affect X if A1, A2, and A3 are unchanged.
    check_unused_inputs_ignored: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed({A4, B1, VPWR, VGND, VPB, VNB}) && $stable({A1, A2, A3})) |-> (X == $past(X))
    );

endmodule