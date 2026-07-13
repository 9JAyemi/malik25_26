module sky130_fd_sc_lp__einvp_sva (
    input logic Z,
    input logic A,
    input logic TE
);
    // When enabled (TE=1), Z must be the bitwise NOT of A.
    check_enable_inverts: assert property (TE === 1'b1 |-> (Z === ~A));

    // When disabled (TE=0), Z must be high-impedance.
    check_disable_tristate: assert property (TE === 1'b0 |-> (Z === 1'bz));

    // Z can be high-impedance only when disabled (TE=0).
    check_z_only_when_disabled: assert property ((Z === 1'bz) |-> (TE === 1'b0));
endmodule