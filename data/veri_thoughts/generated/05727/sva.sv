module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the RTL priority expression.
    check_y_matches_rtl_function: assert property (
        @($global_clock)
        Y == ((A1 & A2) ? 1'b1 :
              (B1 ? 1'b0 :
               (C1 ? ~D1 : 1'b1)))
    );

    // A1 and A2 high force Y high.
    check_a1_a2_path_forces_high: assert property (
        @($global_clock)
        (A1 & A2) |-> (Y == 1'b1)
    );

    // B1 high forces Y low when the A1/A2 path is inactive.
    check_b1_path_forces_low: assert property (
        @($global_clock)
        (!(A1 & A2) && B1) |-> (Y == 1'b0)
    );

    // C1 selects the inverted D1 value when higher-priority paths are inactive.
    check_c1_path_inverts_d1: assert property (
        @($global_clock)
        (!(A1 & A2) && !B1 && C1) |-> (Y == ~D1)
    );

    // The default path drives Y high when no earlier condition is selected.
    check_default_path_forces_high: assert property (
        @($global_clock)
        (!(A1 & A2) && !B1 && !C1) |-> (Y == 1'b1)
    );

endmodule