module sky130_fd_sc_ms__and4_sva (
    input logic CLK,  // sampling clock for assertions
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Analysis: no clock/reset in RTL; pure combinational AND4 with buffer; X = A & B & C & D.

    // X equals the AND of inputs A,B,C,D.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == (A & B & C & D)
    );

    // If all inputs are HIGH, X must be HIGH.
    check_all_inputs_high_implies_X_high: assert property (
        @(posedge CLK) (A & B & C & D) |-> (X == 1'b1)
    );

    // If any input is LOW, X must be LOW.
    check_any_input_low_implies_X_low: assert property (
        @(posedge CLK) (!A || !B || !C || !D) |-> (X == 1'b0)
    );

    // A rising edge on X implies all inputs are HIGH.
    check_X_rise_requires_all_inputs_high: assert property (
        @(posedge CLK) $rose(X) |-> (A & B & C & D)
    );

    // A falling edge on X implies at least one input is LOW.
    check_X_fall_requires_any_input_low: assert property (
        @(posedge CLK) $fell(X) |-> (!A || !B || !C || !D)
    );

    // If all inputs are stable, X is stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(X)
    );

    // When the AND of inputs rises, X rises.
    check_all_high_rise_causes_X_rise: assert property (
        @(posedge CLK) $rose(A & B & C & D) |-> $rose(X)
    );

    // When the AND of inputs falls, X falls.
    check_all_high_fall_causes_X_fall: assert property (
        @(posedge CLK) $fell(A & B & C & D) |-> $fell(X)
    );
endmodule