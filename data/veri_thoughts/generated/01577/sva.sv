module mux2to1_sva (
    input logic CLK,   // Sampling clock for assertions (RTL has no clock/reset)
    input logic A,
    input logic B,
    input logic SEL,
    input logic OUT
);
    // When SEL is 0, OUT must equal A.
    check_sel0_routes_A: assert property (
        @(posedge CLK) (SEL == 1'b0) |-> (OUT == A)
    );

    // When SEL is 1, OUT must equal B.
    check_sel1_routes_B: assert property (
        @(posedge CLK) (SEL == 1'b1) |-> (OUT == B)
    );

    // If SEL=0 and both SEL and A are stable, OUT remains stable.
    check_out_stable_when_sel0_and_A_stable: assert property (
        @(posedge CLK) (SEL == 1'b0 && $stable(SEL) && $stable(A)) |-> $stable(OUT)
    );

    // If SEL=1 and both SEL and B are stable, OUT remains stable.
    check_out_stable_when_sel1_and_B_stable: assert property (
        @(posedge CLK) (SEL == 1'b1 && $stable(SEL) && $stable(B)) |-> $stable(OUT)
    );

    // If SEL=0 is stable and A changes, OUT must change to match A.
    check_out_updates_with_A_when_sel0: assert property (
        @(posedge CLK) (SEL == 1'b0 && $stable(SEL) && !$stable(A)) |-> (!$stable(OUT) && (OUT == A))
    );

    // If SEL=1 is stable and B changes, OUT must change to match B.
    check_out_updates_with_B_when_sel1: assert property (
        @(posedge CLK) (SEL == 1'b1 && $stable(SEL) && !$stable(B)) |-> (!$stable(OUT) && (OUT == B))
    );

    // If SEL=0 is stable and only B changes, OUT remains stable.
    check_out_unchanged_when_unselected_B_changes_sel0: assert property (
        @(posedge CLK) (SEL == 1'b0 && $stable(SEL) && $stable(A) && !$stable(B)) |-> $stable(OUT)
    );

    // If SEL=1 is stable and only A changes, OUT remains stable.
    check_out_unchanged_when_unselected_A_changes_sel1: assert property (
        @(posedge CLK) (SEL == 1'b1 && $stable(SEL) && $stable(B) && !$stable(A)) |-> $stable(OUT)
    );

    // If SEL=0 is stable and OUT changes, A must have changed.
    check_out_change_needs_A_when_sel0: assert property (
        @(posedge CLK) (SEL == 1'b0 && $stable(SEL) && !$stable(OUT)) |-> !$stable(A)
    );

    // If SEL=1 is stable and OUT changes, B must have changed.
    check_out_change_needs_B_when_sel1: assert property (
        @(posedge CLK) (SEL == 1'b1 && $stable(SEL) && !$stable(OUT)) |-> !$stable(B)
    );
endmodule