module comparator_sva (
    input logic CLK,
    input logic RESETn,
    input logic A, B, C, D, E, F, G, H,
    input logic EQ,
    input logic GT
);
    // EQ must equal bitwise equality across all four positions.
    check_eq_matches_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        EQ == ((A == E) && (B == F) && (C == G) && (D == H))
    );

    // GT must match the coded lexicographic comparison (with final D >= H).
    check_gt_matches_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        GT == (
            (A > E) ||
            ((A == E) && (
                (B > F) ||
                ((B == F) && (
                    (C > G) ||
                    ((C == G) && (D >= H))
                ))
            ))
        )
    );

    // When all four positions are equal, GT must be high (due to D >= H).
    check_eq_implies_gt: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B == F) && (C == G) && (D == H)) |-> (GT == 1'b1)
    );

    // If A > E, GT must be high.
    check_a_gt_e_implies_gt: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A > E) |-> (GT == 1'b1)
    );

    // If A == E and B > F, GT must be high.
    check_b_gt_f_implies_gt_when_a_eq_e: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B > F)) |-> (GT == 1'b1)
    );

    // If A == E, B == F, and C > G, GT must be high.
    check_c_gt_g_implies_gt_when_prefix_equal: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B == F) && (C > G)) |-> (GT == 1'b1)
    );

    // If A == E, B == F, C == G, and D >= H, GT must be high.
    check_d_ge_h_implies_gt_when_prefix_equal: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B == F) && (C == G) && (D >= H)) |-> (GT == 1'b1)
    );

    // If A < E, GT must be low.
    check_a_lt_e_implies_not_gt: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A < E) |-> (GT == 1'b0)
    );

    // If A == E and B < F, GT must be low.
    check_b_lt_f_implies_not_gt_when_a_eq_e: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B < F)) |-> (GT == 1'b0)
    );

    // If A == E, B == F, and C < G, GT must be low.
    check_c_lt_g_implies_not_gt_when_prefix_equal: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B == F) && (C < G)) |-> (GT == 1'b0)
    );

    // If A == E, B == F, C == G, and D < H, GT must be low.
    check_d_lt_h_implies_not_gt_when_prefix_equal: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == E) && (B == F) && (C == G) && (D < H)) |-> (GT == 1'b0)
    );
endmodule