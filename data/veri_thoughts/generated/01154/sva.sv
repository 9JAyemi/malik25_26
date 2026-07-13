module sky130_fd_sc_lp__einvp_sva (
    input logic Z,
    input logic A,
    input logic TE
);
    // When TE rises HIGH, Z equals bitwise NOT of A.
    check_invert_on_te_rise: assert property (
        @(posedge TE) (TE == 1'b1) |-> (Z === ~A)
    );

    // When TE is HIGH, Z equals ~A on A rising edges.
    check_invert_on_a_rise_when_enabled: assert property (
        @(posedge A) (TE == 1'b1) |-> (Z === ~A)
    );

    // When TE is HIGH, Z equals ~A on A falling edges.
    check_invert_on_a_fall_when_enabled: assert property (
        @(negedge A) (TE == 1'b1) |-> (Z === ~A)
    );

    // When TE falls LOW, Z goes high-impedance.
    check_highz_on_te_fall: assert property (
        @(negedge TE) (TE == 1'b0) |-> (Z === 1'bz)
    );

    // When TE is LOW, Z is high-impedance on A rising edges.
    check_highz_on_a_rise_when_disabled: assert property (
        @(posedge A) (TE == 1'b0) |-> (Z === 1'bz)
    );

    // When TE is LOW, Z is high-impedance on A falling edges.
    check_highz_on_a_fall_when_disabled: assert property (
        @(negedge A) (TE == 1'b0) |-> (Z === 1'bz)
    );

    // When TE is HIGH, Z is not high-impedance.
    check_not_highz_when_enabled_te_rise: assert property (
        @(posedge TE) (TE == 1'b1) |-> (Z !== 1'bz)
    );
endmodule