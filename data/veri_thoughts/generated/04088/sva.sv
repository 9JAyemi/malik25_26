module minimum_value_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] min
);

    // Sample the combinational behavior on the formal global clock.
    // min must follow the RTL's minimum-selection function.
    check_min_function: assert property (
        @($global_clock)
        min == (((a <= b) && (a <= c)) ? a :
                (((b <= a) && (b <= c)) ? b : c))
    );

    // When a is smallest or tied for smallest, min must be a.
    check_select_a: assert property (
        @($global_clock)
        ((a <= b) && (a <= c)) |-> (min == a)
    );

    // When a is not selected and b is smallest or tied, min must be b.
    check_select_b: assert property (
        @($global_clock)
        (!((a <= b) && (a <= c)) && ((b <= a) && (b <= c))) |-> (min == b)
    );

    // When neither a nor b is selected, min must be c.
    check_select_c: assert property (
        @($global_clock)
        (!((a <= b) && (a <= c)) && !((b <= a) && (b <= c))) |-> (min == c)
    );

    // The selected minimum must not exceed a.
    check_min_le_a: assert property (
        @($global_clock)
        (min <= a)
    );

    // The selected minimum must not exceed b.
    check_min_le_b: assert property (
        @($global_clock)
        (min <= b)
    );

    // The selected minimum must not exceed c.
    check_min_le_c: assert property (
        @($global_clock)
        (min <= c)
    );

    // The output must match one of the three inputs.
    check_min_matches_input: assert property (
        @($global_clock)
        ((min == a) || (min == b) || (min == c))
    );

endmodule