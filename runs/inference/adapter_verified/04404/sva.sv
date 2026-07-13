module or3_2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

// X must equal A | B | C.
    check_x_matches_or3: assert property (
        @(posedge clk) X == (A | B | C)
    );

// If all inputs are 0, X must be 0.
    check_x_zero_when_all_zero: assert property (
        @(posedge clk) (!A && !B && !C) |-> (X == 1'b0)
    );

// If any input is 1, X must be 1.
    check_x_one_when_any_one: assert property (
        @(posedge clk) (A || B || C) |-> (X == 1'b1)
    );

// A high must force X high.
    check_x_high_when_a_high: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

// B high must force X high.
    check_x_high_when_b_high: assert property (
        @(posedge clk) B |-> (X == 1'b1)
    );

// C high must force X high.
    check_x_high_when_c_high: assert property (
        @(posedge clk) C |-> (X == 1'b1)
    );

// X low implies all inputs are low.
    check_x_low_implies_all_zero: assert property (
        @(posedge clk) (!X) |-> (!A && !B && !C)
    );

// X high implies at least one input is high.
    check_x_high_implies_any_one: assert property (
        @(posedge clk) X |-> (A || B || C)
    );

endmodule
