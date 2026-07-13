module logic_gate_sva (
    input  logic CLK,          // External property clock
    input  logic X,            // DUT ports
    input  logic A1,
    input  logic A2,
    input  logic A3,
    input  logic A4,
    input  logic B1,
    input  logic and0_out,     // DUT internal nets
    input  logic or0_out_X,
    input  logic VPWR,         // DUT supplies (used for disable iff)
    input  logic VGND
);
    // Combinational gate: X = (A1 & A2 & A3 & A4) | B1; no reset in RTL; assertions clocked on CLK, disabled when VPWR is low.

    // X matches the Boolean function of inputs.
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!VPWR) X == ((A1 & A2 & A3 & A4) | B1)
    );

    // B1 HIGH forces X HIGH.
    check_b1_dominates_x: assert property (
        @(posedge CLK) disable iff (!VPWR) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // All A inputs HIGH force X HIGH.
    check_all_a_high_sets_x: assert property (
        @(posedge CLK) disable iff (!VPWR) (A1 & A2 & A3 & A4) |-> (X == 1'b1)
    );

    // When B1 is LOW, X equals the AND of A inputs.
    check_b1_low_equals_and: assert property (
        @(posedge CLK) disable iff (!VPWR) (B1 == 1'b0) |-> (X == (A1 & A2 & A3 & A4))
    );

    // X LOW implies B1 is LOW and not all A inputs are HIGH.
    check_x_low_implication: assert property (
        @(posedge CLK) disable iff (!VPWR) (X == 1'b0) |-> ((B1 == 1'b0) && !(A1 & A2 & A3 & A4))
    );

    // X HIGH implies B1 is HIGH or all A inputs are HIGH.
    check_x_high_implication: assert property (
        @(posedge CLK) disable iff (!VPWR) (X == 1'b1) |-> ((B1 == 1'b1) || (A1 & A2 & A3 & A4))
    );

    // Rising edge of B1 sets X HIGH.
    check_b1_rise_sets_x: assert property (
        @(posedge CLK) disable iff (!VPWR) $rose(B1) |-> (X == 1'b1)
    );

    // Rising edge of X implies B1 HIGH or all A inputs HIGH.
    check_x_rise_cause: assert property (
        @(posedge CLK) disable iff (!VPWR) $rose(X) |-> ((B1 == 1'b1) || (A1 & A2 & A3 & A4))
    );

    // Falling edge of X implies B1 LOW and not all A inputs HIGH.
    check_x_fall_cause: assert property (
        @(posedge CLK) disable iff (!VPWR) $fell(X) |-> ((B1 == 1'b0) && !(A1 & A2 & A3 & A4))
    );

    // X only changes when at least one input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) disable iff (!VPWR) $changed(X) |-> $changed({A1, A2, A3, A4, B1})
    );

    // Internal AND gate implements A1&A2&A3&A4.
    check_internal_and_def: assert property (
        @(posedge CLK) disable iff (!VPWR) and0_out == (A1 & A2 & A3 & A4)
    );

    // Internal OR gate implements and0_out|B1.
    check_internal_or_def: assert property (
        @(posedge CLK) disable iff (!VPWR) or0_out_X == (and0_out | B1)
    );

    // Output buffer drives X equal to or0_out_X.
    check_internal_buf_def: assert property (
        @(posedge CLK) disable iff (!VPWR) X == or0_out_X
    );
endmodule