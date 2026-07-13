module and_gate_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic Y
);

    // Y must equal the AND of all four inputs.
    check_y_matches_four_input_and: assert property (
        @(posedge clk) Y == (A1 & A2 & A3 & A4)
    );

    // All inputs high must drive Y high.
    check_y_high_when_all_inputs_high: assert property (
        @(posedge clk) (A1 && A2 && A3 && A4) |-> Y
    );

    // A high Y requires all inputs to be high.
    check_y_high_only_when_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A1 && A2 && A3 && A4)
    );

    // Any low input must force Y low.
    check_y_low_when_any_input_low: assert property (
        @(posedge clk) (!A1 || !A2 || !A3 || !A4) |-> !Y
    );

endmodule