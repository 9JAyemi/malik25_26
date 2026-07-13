module delay_gate_4stage_sva (
    input logic clk,
    input logic A,
    input logic X
);

    // X equals A sampled four clocks earlier.
    check_four_cycle_delay: assert property (
        @(posedge clk) 1'b1 |-> ##4 (X == $past(A, 4))
    );

    // A high sample must appear at X four clocks later.
    check_high_propagation: assert property (
        @(posedge clk) A |-> ##4 X
    );

    // A low sample must appear at X four clocks later.
    check_low_propagation: assert property (
        @(posedge clk) !A |-> ##4 !X
    );

    // A rising edge must propagate to X after four clocks.
    check_rise_propagation: assert property (
        @(posedge clk) $rose(A) |-> ##4 $rose(X)
    );

    // A falling edge must propagate to X after four clocks.
    check_fall_propagation: assert property (
        @(posedge clk) $fell(A) |-> ##4 $fell(X)
    );

endmodule