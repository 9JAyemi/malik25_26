module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

// Y must equal the AND of A, B, and C.
    check_y_matches_and: assert property (
        @(posedge clk) Y == (A & B & C)
    );

// A high with B and C high must drive Y high.
    check_y_high_when_all_inputs_high: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

// A low must force Y low.
    check_y_low_when_a_low: assert property (
        @(posedge clk) !A |-> !Y
    );

// B low must force Y low.
    check_y_low_when_b_low: assert property (
        @(posedge clk) !B |-> !Y
    );

// C low must force Y low.
    check_y_low_when_c_low: assert property (
        @(posedge clk) !C |-> !Y
    );

endmodule
