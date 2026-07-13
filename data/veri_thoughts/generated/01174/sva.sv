module sky130_fd_sc_ls__or3_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // OR truth table: output equals A|B|C every cycle.
    check_or_function_equivalence: assert property (
        @(posedge CLK) X == (A | B | C)
    );

    // When all inputs are 0, output must be 0.
    check_all_zero_implies_x_zero: assert property (
        @(posedge CLK) (!A && !B && !C) |-> (X == 1'b0)
    );

    // Rising edge on X must be caused by a rising edge on at least one input.
    check_x_rise_caused_by_input_rise: assert property (
        @(posedge CLK) $rose(X) |-> ($rose(A) || $rose(B) || $rose(C))
    );

    // Falling edge on X must be caused by a falling edge on at least one input.
    check_x_fall_caused_by_input_fall: assert property (
        @(posedge CLK) $fell(X) |-> ($fell(A) || $fell(B) || $fell(C))
    );

    // If inputs are stable, output remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) (!$initstate) && $stable(A) && $stable(B) && $stable(C) |-> $stable(X)
    );
endmodule