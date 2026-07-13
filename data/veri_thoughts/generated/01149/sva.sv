module feedforward_mux_4to1_sel2_32_1_sva (
    input logic [31:0] din1,
    input logic [31:0] din2,
    input logic [31:0] din3,
    input logic [31:0] din4,
    input logic [1:0]  din5,
    input logic [31:0] dout
);

    ///// Functional mapping /////
    // Direct functional equivalence to the ternary expression.
    check_mux_function: assert property (
        @($global_clock) dout == (din5[1] ? (din5[0] ? din4 : din3) : (din5[0] ? din2 : din1))
    );

    // When din5 == 2'b00, dout equals din1.
    check_sel00_maps_din1: assert property (
        @($global_clock) (din5 == 2'b00) |-> (dout == din1)
    );

    // When din5 == 2'b01, dout equals din2.
    check_sel01_maps_din2: assert property (
        @($global_clock) (din5 == 2'b01) |-> (dout == din2)
    );

    // When din5 == 2'b10, dout equals din3.
    check_sel10_maps_din3: assert property (
        @($global_clock) (din5 == 2'b10) |-> (dout == din3)
    );

    // When din5 == 2'b11, dout equals din4.
    check_sel11_maps_din4: assert property (
        @($global_clock) (din5 == 2'b11) |-> (dout == din4)
    );

    ///// Independence/stability /////
    // If sel[1]==0 and sel,din1,din2 are stable, dout is stable (din3/din4 do not affect).
    check_unselected_pair_no_effect_sel1_is0: assert property (
        @($global_clock) (din5[1] == 1'b0 && $stable(din5) && $stable(din1) && $stable(din2)) |-> $stable(dout)
    );

    // If sel[1]==1 and sel,din3,din4 are stable, dout is stable (din1/din2 do not affect).
    check_unselected_pair_no_effect_sel1_is1: assert property (
        @($global_clock) (din5[1] == 1'b1 && $stable(din5) && $stable(din3) && $stable(din4)) |-> $stable(dout)
    );

    // If sel[0]==0 and sel,din1,din3 are stable, dout is stable (din2/din4 do not affect).
    check_unselected_with_sel0_is0: assert property (
        @($global_clock) (din5[0] == 1'b0 && $stable(din5) && $stable(din1) && $stable(din3)) |-> $stable(dout)
    );

    // If sel[0]==1 and sel,din2,din4 are stable, dout is stable (din1/din3 do not affect).
    check_unselected_with_sel0_is1: assert property (
        @($global_clock) (din5[0] == 1'b1 && $stable(din5) && $stable(din2) && $stable(din4)) |-> $stable(dout)
    );

    // If all inputs are stable, dout remains stable (purely combinational behavior).
    check_quiescent_stability: assert property (
        @($global_clock) $stable({din1,din2,din3,din4,din5}) |-> $stable(dout)
    );

endmodule