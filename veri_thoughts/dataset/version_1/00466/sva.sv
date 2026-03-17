module top_sva (
    input logic       di,
    input logic [3:0] do
);

    // do[0] is the inverted input.
    check_do0_inverts_di: assert property (
        @($global_clock) do[0] == ~di
    );

    // do[1] is the inverted input.
    check_do1_inverts_di: assert property (
        @($global_clock) do[1] == ~di
    );

    // do[2] is the inverted input from c_inst.
    check_do2_inverts_di: assert property (
        @($global_clock) do[2] == ~di
    );

    // do[3] matches the original input.
    check_do3_matches_di: assert property (
        @($global_clock) do[3] == di
    );

    // The two box outputs must match.
    check_do0_do1_match: assert property (
        @($global_clock) do[0] == do[1]
    );

    // c_inst low output must match the box outputs.
    check_do1_do2_match: assert property (
        @($global_clock) do[1] == do[2]
    );

    // c_inst high output must complement the low outputs.
    check_do3_complements_do2: assert property (
        @($global_clock) do[3] == ~do[2]
    );

    // The full output bus matches the implemented combinational function.
    check_output_bus_function: assert property (
        @($global_clock) do == {di, ~di, ~di, ~di}
    );

endmodule