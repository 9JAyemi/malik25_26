// _NOT_, _AND_, _OR_, _XOR_, and _MUX_ are combinational and have no RTL clock port for clocked SVA.

// _DFF_N_: falling-edge DFF without reset.
module _DFF_N__assertions (
    input logic D,
    input logic Q,
    input logic C
);
    // Q reflects D sampled on the previous falling edge of C.
    check_q_captures_d_on_falling_c: assert property (
        @(negedge C) disable iff ($initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_N_ _DFF_N__assertions _DFF_N__assertions_i (
    .D(D),
    .Q(Q),
    .C(C)
);

// _DFF_P_: rising-edge DFF without reset.
module _DFF_P__assertions (
    input logic D,
    input logic Q,
    input logic C
);
    // Q reflects D sampled on the previous rising edge of C.
    check_q_captures_d_on_rising_c: assert property (
        @(posedge C) disable iff ($initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_P_ _DFF_P__assertions _DFF_P__assertions_i (
    .D(D),
    .Q(Q),
    .C(C)
);

// _DFF_NN0_: falling-edge DFF with active-low reset to 0.
module _DFF_NN0__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 0 while active-low reset is asserted.
    check_q_is_zero_during_active_low_reset: assert property (
        @(negedge C) disable iff (R || $initstate)
        Q == 1'b0
    );

    // Without reset interference, Q reflects D from the previous falling edge of C.
    check_q_captures_d_on_falling_c: assert property (
        @(negedge C) disable iff (!R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_NN0_ _DFF_NN0__assertions _DFF_NN0__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_NN1_: falling-edge DFF with active-low reset to 1.
module _DFF_NN1__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 1 while active-low reset is asserted.
    check_q_is_one_during_active_low_reset: assert property (
        @(negedge C) disable iff (R || $initstate)
        Q == 1'b1
    );

    // Without reset interference, Q reflects D from the previous falling edge of C.
    check_q_captures_d_on_falling_c: assert property (
        @(negedge C) disable iff (!R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_NN1_ _DFF_NN1__assertions _DFF_NN1__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_NP0_: falling-edge DFF with active-high reset to 0.
module _DFF_NP0__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 0 while active-high reset is asserted.
    check_q_is_zero_during_active_high_reset: assert property (
        @(negedge C) disable iff (!R || $initstate)
        Q == 1'b0
    );

    // Without reset interference, Q reflects D from the previous falling edge of C.
    check_q_captures_d_on_falling_c: assert property (
        @(negedge C) disable iff (R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_NP0_ _DFF_NP0__assertions _DFF_NP0__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_NP1_: falling-edge DFF with active-high reset to 1.
module _DFF_NP1__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 1 while active-high reset is asserted.
    check_q_is_one_during_active_high_reset: assert property (
        @(negedge C) disable iff (!R || $initstate)
        Q == 1'b1
    );

    // Without reset interference, Q reflects D from the previous falling edge of C.
    check_q_captures_d_on_falling_c: assert property (
        @(negedge C) disable iff (R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_NP1_ _DFF_NP1__assertions _DFF_NP1__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_PN0_: rising-edge DFF with active-low reset to 0.
module _DFF_PN0__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 0 while active-low reset is asserted.
    check_q_is_zero_during_active_low_reset: assert property (
        @(posedge C) disable iff (R || $initstate)
        Q == 1'b0
    );

    // Without reset interference, Q reflects D from the previous rising edge of C.
    check_q_captures_d_on_rising_c: assert property (
        @(posedge C) disable iff (!R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_PN0_ _DFF_PN0__assertions _DFF_PN0__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_PN1_: rising-edge DFF with active-low reset to 1.
module _DFF_PN1__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 1 while active-low reset is asserted.
    check_q_is_one_during_active_low_reset: assert property (
        @(posedge C) disable iff (R || $initstate)
        Q == 1'b1
    );

    // Without reset interference, Q reflects D from the previous rising edge of C.
    check_q_captures_d_on_rising_c: assert property (
        @(posedge C) disable iff (!R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_PN1_ _DFF_PN1__assertions _DFF_PN1__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_PP0_: rising-edge DFF with active-high reset to 0.
module _DFF_PP0__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 0 while active-high reset is asserted.
    check_q_is_zero_during_active_high_reset: assert property (
        @(posedge C) disable iff (!R || $initstate)
        Q == 1'b0
    );

    // Without reset interference, Q reflects D from the previous rising edge of C.
    check_q_captures_d_on_rising_c: assert property (
        @(posedge C) disable iff (R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_PP0_ _DFF_PP0__assertions _DFF_PP0__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);

// _DFF_PP1_: rising-edge DFF with active-high reset to 1.
module _DFF_PP1__assertions (
    input logic D,
    input logic Q,
    input logic C,
    input logic R
);
    // Q is 1 while active-high reset is asserted.
    check_q_is_one_during_active_high_reset: assert property (
        @(posedge C) disable iff (!R || $initstate)
        Q == 1'b1
    );

    // Without reset interference, Q reflects D from the previous rising edge of C.
    check_q_captures_d_on_rising_c: assert property (
        @(posedge C) disable iff (R || $initstate)
        1'b1 |=> (Q == $past(D))
    );
endmodule

bind _DFF_PP1_ _DFF_PP1__assertions _DFF_PP1__assertions_i (
    .D(D),
    .Q(Q),
    .C(C),
    .R(R)
);