module sky130_fd_sc_hd__lpflow_clkinvkapwr_sva (
    input logic CLK,   // external clock for sampling
    input logic A,
    input logic Y
);
    // Y is always the logical inversion of A.
    check_complement_always: assert property (
        @(posedge CLK) (Y === ~A)
    );

    // When A is 0, Y must be 1.
    check_y1_when_a0: assert property (
        @(posedge CLK) (A === 1'b0) |-> (Y === 1'b1)
    );

    // When A is 1, Y must be 0.
    check_y0_when_a1: assert property (
        @(posedge CLK) (A === 1'b1) |-> (Y === 1'b0)
    );

    // If A falls, Y must rise.
    check_y_rise_on_a_fall: assert property (
        @(posedge CLK) $fell(A) |-> $rose(Y)
    );

    // If A rises, Y must fall.
    check_y_fall_on_a_rise: assert property (
        @(posedge CLK) $rose(A) |-> $fell(Y)
    );

    // If A changes, Y must change.
    check_y_changes_when_a_changes: assert property (
        @(posedge CLK) $changed(A) |-> $changed(Y)
    );

    // Y cannot change unless A changes.
    check_no_y_change_without_a_change: assert property (
        @(posedge CLK) $changed(Y) |-> $changed(A)
    );

    // Known A implies known Y.
    check_known_y_when_known_a: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> (!$isunknown(Y))
    );

    // Known Y implies known A.
    check_known_a_when_known_y: assert property (
        @(posedge CLK) (!$isunknown(Y)) |-> (!$isunknown(A))
    );

    // When both are known, A and Y must differ.
    check_known_values_inequal: assert property (
        @(posedge CLK) (!($isunknown({A,Y}))) |-> (A != Y)
    );
endmodule