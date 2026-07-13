module mux_2to1_sva (
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);
    // On A rising edge, Y must equal the mux function.
    check_func_on_A_rise: assert property (
        @(posedge A) Y == (SEL ? B : A)
    );
    // On A falling edge, Y must equal the mux function.
    check_func_on_A_fall: assert property (
        @(negedge A) Y == (SEL ? B : A)
    );
    // On B rising edge, Y must equal the mux function.
    check_func_on_B_rise: assert property (
        @(posedge B) Y == (SEL ? B : A)
    );
    // On B falling edge, Y must equal the mux function.
    check_func_on_B_fall: assert property (
        @(negedge B) Y == (SEL ? B : A)
    );
    // On SEL rising edge, Y must equal the mux function (select B).
    check_func_on_SEL_rise: assert property (
        @(posedge SEL) Y == (SEL ? B : A)
    );
    // On SEL falling edge, Y must equal the mux function (select A).
    check_func_on_SEL_fall: assert property (
        @(negedge SEL) Y == (SEL ? B : A)
    );

    // When SEL=0 and A rises, Y must go HIGH.
    track_Y_with_A_when_SEL0_rise: assert property (
        @(posedge A) (SEL == 1'b0) |-> (Y == 1'b1)
    );
    // When SEL=0 and A falls, Y must go LOW.
    track_Y_with_A_when_SEL0_fall: assert property (
        @(negedge A) (SEL == 1'b0) |-> (Y == 1'b0)
    );
    // When SEL=1 and B rises, Y must go HIGH.
    track_Y_with_B_when_SEL1_rise: assert property (
        @(posedge B) (SEL == 1'b1) |-> (Y == 1'b1)
    );
    // When SEL=1 and B falls, Y must go LOW.
    track_Y_with_B_when_SEL1_fall: assert property (
        @(negedge B) (SEL == 1'b1) |-> (Y == 1'b0)
    );
endmodule