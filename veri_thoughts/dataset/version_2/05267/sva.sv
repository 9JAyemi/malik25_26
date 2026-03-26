module isolator_sva (
    input logic        rc_ackn_rr,
    input logic        rc_ackn,
    input logic        p_prdy,
    input logic [31:0] p_data,
    input logic        c_crdy,
    input logic        c_cerr,
    input logic        p_prdy_rr,
    input logic [31:0] p_data_rr,
    input logic        c_crdy_rr,
    input logic        c_cerr_rr,
    input logic        is_reconfn
);

    // rc_ackn is forced high when isolation is active.
    check_rc_ackn_isolated: assert property (
        @($global_clock) (!is_reconfn) |-> (rc_ackn == 1'b1)
    );

    // rc_ackn passes through in normal mode.
    check_rc_ackn_passthrough: assert property (
        @($global_clock) is_reconfn |-> (rc_ackn == rc_ackn_rr)
    );

    // p_prdy is forced low when isolation is active.
    check_p_prdy_isolated: assert property (
        @($global_clock) (!is_reconfn) |-> (p_prdy == 1'b0)
    );

    // p_prdy passes through in normal mode.
    check_p_prdy_passthrough: assert property (
        @($global_clock) is_reconfn |-> (p_prdy == p_prdy_rr)
    );

    // p_data is forced to zero when isolation is active.
    check_p_data_isolated: assert property (
        @($global_clock) (!is_reconfn) |-> (p_data == 32'h00000000)
    );

    // p_data passes through in normal mode.
    check_p_data_passthrough: assert property (
        @($global_clock) is_reconfn |-> (p_data == p_data_rr)
    );

    // c_crdy is forced low when isolation is active.
    check_c_crdy_isolated: assert property (
        @($global_clock) (!is_reconfn) |-> (c_crdy == 1'b0)
    );

    // c_crdy passes through in normal mode.
    check_c_crdy_passthrough: assert property (
        @($global_clock) is_reconfn |-> (c_crdy == c_crdy_rr)
    );

    // c_cerr is forced high when isolation is active.
    check_c_cerr_isolated: assert property (
        @($global_clock) (!is_reconfn) |-> (c_cerr == 1'b1)
    );

    // c_cerr passes through in normal mode.
    check_c_cerr_passthrough: assert property (
        @($global_clock) is_reconfn |-> (c_cerr == c_cerr_rr)
    );

endmodule