module bufinv_sva (
    input logic Y,
    input logic A
);
    // Analysis: no clock or reset in RTL; pure combinational invert (Y = ~A).

    ///// Inversion relation sampled on A edges /////
    // When A rises, Y must be 0 (since Y = ~A).
    check_y_low_on_a_rise: assert property (
        @(posedge A) (Y == 1'b0)
    );
    // When A falls, Y must be 1 (since Y = ~A).
    check_y_high_on_a_fall: assert property (
        @(negedge A) (Y == 1'b1)
    );
    // On A rising edge, Y equals bitwise NOT of A.
    check_y_eq_not_a_on_a_rise: assert property (
        @(posedge A) (Y == ~A)
    );
    // On A falling edge, Y equals bitwise NOT of A.
    check_y_eq_not_a_on_a_fall: assert property (
        @(negedge A) (Y == ~A)
    );

    ///// Inversion relation sampled on Y edges /////
    // When Y rises, A must be 0 (since A = ~Y).
    check_a_low_on_y_rise: assert property (
        @(posedge Y) (A == 1'b0)
    );
    // When Y falls, A must be 1 (since A = ~Y).
    check_a_high_on_y_fall: assert property (
        @(negedge Y) (A == 1'b1)
    );
endmodule