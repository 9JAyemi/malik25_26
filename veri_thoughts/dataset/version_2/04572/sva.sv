module nor2_gate_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

    // Y must always match the NOR of A and B.
    check_nor_equation: assert property (
        @(posedge clk) Y == ~(A | B)
    );

    // Y must be high when both inputs are low.
    check_output_high_when_both_low: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // Y must be low whenever A is high.
    check_output_low_when_a_high: assert property (
        @(posedge clk) A |-> !Y
    );

    // Y must be low whenever B is high.
    check_output_low_when_b_high: assert property (
        @(posedge clk) B |-> !Y
    );

    // A high Y implies both inputs are low.
    check_output_high_only_when_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B)
    );

endmodule