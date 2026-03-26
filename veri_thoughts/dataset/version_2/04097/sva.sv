module parity_checker_sva (
    input logic [3:0] IN,
    input logic OUT,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // OUT matches the implemented logic function.
    check_out_matches_three_input_and_or_function: assert property (
        @($global_clock)
        OUT == ((IN[0] & IN[1] & IN[2]) |
                (IN[1] & IN[2] & IN[3]) |
                (IN[2] & IN[3] & IN[0]) |
                (IN[3] & IN[0] & IN[1]))
    );

    // OUT is low when no three-input product term is true.
    check_no_three_high_keeps_out_low: assert property (
        @($global_clock)
        !((IN[0] & IN[1] & IN[2]) |
          (IN[1] & IN[2] & IN[3]) |
          (IN[2] & IN[3] & IN[0]) |
          (IN[3] & IN[0] & IN[1])) |-> !OUT
    );

    // OUT is high when all four inputs are high.
    check_all_four_high_sets_out: assert property (
        @($global_clock)
        (&IN) |-> OUT
    );

    // OUT is high when IN[1], IN[2], and IN[3] are high.
    check_in123_high_sets_out: assert property (
        @($global_clock)
        (!IN[0] && IN[1] && IN[2] && IN[3]) |-> OUT
    );

    // OUT is high when IN[0], IN[2], and IN[3] are high.
    check_in023_high_sets_out: assert property (
        @($global_clock)
        (IN[0] && !IN[1] && IN[2] && IN[3]) |-> OUT
    );

    // OUT is high when IN[0], IN[1], and IN[3] are high.
    check_in013_high_sets_out: assert property (
        @($global_clock)
        (IN[0] && IN[1] && !IN[2] && IN[3]) |-> OUT
    );

    // OUT is high when IN[0], IN[1], and IN[2] are high.
    check_in012_high_sets_out: assert property (
        @($global_clock)
        (IN[0] && IN[1] && IN[2] && !IN[3]) |-> OUT
    );

endmodule