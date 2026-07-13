module and_gate_sva (
    input logic A,
    input logic B,
    input logic Y
);

    // No clock/reset in RTL; sample on any input or output edge.
    // Y must implement the AND of A and B.
    check_output_matches_and_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
        Y == (A & B)
    );

    // If either input is low, Y must be low.
    check_low_input_forces_output_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
        ((!A) || (!B)) |-> (!Y)
    );

    // Y can only be high when both inputs are high.
    check_output_high_requires_both_inputs_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
        Y |-> (A && B)
    );

    // Both inputs high must drive Y high.
    check_both_inputs_high_drive_output_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)
        (A && B) |-> Y
    );

endmodule