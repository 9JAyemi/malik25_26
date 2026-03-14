module mux_2to1_sva (
    input  logic CLK,   // external sampling clock for assertions
    input  logic A,
    input  logic B,
    input  logic SEL,
    input  logic OUT
);
    // When SEL is 1, OUT must equal B in the same cycle.
    check_out_eq_B_when_sel1: assert property (
        @(posedge CLK) (SEL == 1'b1) |-> (OUT == B)
    );

    // When SEL is 0, OUT must equal A in the same cycle.
    check_out_eq_A_when_sel0: assert property (
        @(posedge CLK) (SEL == 1'b0) |-> (OUT == A)
    );

    // OUT equals the mux function of SEL, A, and B.
    check_out_matches_mux_function: assert property (
        @(posedge CLK) (OUT == (SEL ? B : A))
    );

    // On SEL rising edge with A and B stable, OUT updates from A to B.
    check_sel_rise_updates_out_to_B: assert property (
        @(posedge CLK) (!$initstate && $rose(SEL) && $stable(A) && $stable(B)) |-> (OUT == B && $past(OUT) == A)
    );

    // On SEL falling edge with A and B stable, OUT updates from B to A.
    check_sel_fall_updates_out_to_A: assert property (
        @(posedge CLK) (!$initstate && $fell(SEL) && $stable(A) && $stable(B)) |-> (OUT == A && $past(OUT) == B)
    );
endmodule