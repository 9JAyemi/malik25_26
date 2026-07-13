module four_to_one_assertions (
    input logic out1,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic VPWR,
    input logic VGND
);

    // Output must match the RTL Boolean equation.
    check_out1_matches_rtl_expr: assert property (
        @($global_clock)
        out1 == (
            (
                ((in1 & in2 & in3) | (in1 & in2 & in4) | (in1 & in3 & in4) | (in2 & in3 & in4))
                | (in1 | in2 | in3 | in4)
                | (~in1 & ~in2 & ~in3 & ~in4)
            )
            & ~((in1 & in2) | (in1 & in3) | (in1 & in4) | (in2 & in3) | (in2 & in4) | (in3 & in4))
        )
    );

    // All inputs low must drive the output high.
    check_all_low_drives_high: assert property (
        @($global_clock)
        (~in1 & ~in2 & ~in3 & ~in4) |-> out1
    );

    // Any one-hot input combination must drive the output high.
    check_one_high_drives_high: assert property (
        @($global_clock)
        (
            ( in1 & ~in2 & ~in3 & ~in4) |
            (~in1 &  in2 & ~in3 & ~in4) |
            (~in1 & ~in2 &  in3 & ~in4) |
            (~in1 & ~in2 & ~in3 &  in4)
        ) |-> out1
    );

    // Any exact two-high input combination must drive the output low.
    check_two_high_drives_low: assert property (
        @($global_clock)
        (
            ( in1 &  in2 & ~in3 & ~in4) |
            ( in1 & ~in2 &  in3 & ~in4) |
            ( in1 & ~in2 & ~in3 &  in4) |
            (~in1 &  in2 &  in3 & ~in4) |
            (~in1 &  in2 & ~in3 &  in4) |
            (~in1 & ~in2 &  in3 &  in4)
        ) |-> !out1
    );

    // Any exact three-high input combination must drive the output low.
    check_three_high_drives_low: assert property (
        @($global_clock)
        (
            (~in1 &  in2 &  in3 &  in4) |
            ( in1 & ~in2 &  in3 &  in4) |
            ( in1 &  in2 & ~in3 &  in4) |
            ( in1 &  in2 &  in3 & ~in4)
        ) |-> !out1
    );

    // All inputs high must drive the output low.
    check_all_high_drives_low: assert property (
        @($global_clock)
        (in1 & in2 & in3 & in4) |-> !out1
    );

endmodule