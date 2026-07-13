module OR3_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// X equals A | B | C.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

// If all inputs are 0, X must be 0.
    check_all_zero_implies_x_zero: assert property (
        @(posedge clk) (!A && !B && !C) |-> (X == 1'b0)
    );

// If any input is 1, X must be 1.
    check_any_one_implies_x_one: assert property (
        @(posedge clk) (A || B || C) |-> (X == 1'b1)
    );

// A rising edge on X implies at least one input is 1.
    check_x_rise_requires_any_one: assert property (
        @(posedge clk) $rose(X) |-> (A || B || C)
    );

// A falling edge on X implies all inputs are 0.
    check_x_fall_requires_all_zero: assert property (
        @(posedge clk) $fell(X) |-> (!A && !B && !C)
    );

endmodule
