module parity_checker_sva (
    input logic [7:0] data_in,
    input logic       sel_b1,
    input logic       parity
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // parity must match the selected XOR of data_in bits.
    check_parity_matches_selected_xor: assert property (
        @($global_clock) parity == (sel_b1 ? ~^data_in : ^data_in)
    );

    // With select low, parity must equal the XOR of all data bits.
    check_parity_when_sel_low: assert property (
        @($global_clock) !sel_b1 |-> (parity == ^data_in)
    );

    // With select high, parity must equal the inverted XOR of all data bits.
    check_parity_when_sel_high: assert property (
        @($global_clock) sel_b1 |-> (parity == ~^data_in)
    );

    // With select low and all data bits low, parity must be low.
    check_parity_zero_when_sel_low: assert property (
        @($global_clock) (!sel_b1 && !|data_in) |-> (parity == 1'b0)
    );

    // With select low and all data bits high, parity must be high.
    check_parity_one_when_sel_low: assert property (
        @($global_clock) (!sel_b1 && |data_in) |-> (parity == 1'b1)
    );

    // With select high and all data bits low, parity must be high.
    check_parity_one_when_sel_high: assert property (
        @($global_clock) (sel_b1 && !|data_in) |-> (parity == 1'b1)
    );

    // With select high and all data bits high, parity must be low.
    check_parity_zero_when_sel_high: assert property (
        @($global_clock) (sel_b1 && |data_in) |-> (parity == 1'b0)
    );

endmodule