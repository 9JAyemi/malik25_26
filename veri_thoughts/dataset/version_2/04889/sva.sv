module comparator_sva (
    input logic       clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic       EQ
);

    // EQ must be high when A and B are equal.
    check_eq_high_when_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ == 1'b1)
    );

    // EQ must be low when A and B are different.
    check_eq_low_when_different: assert property (
        @(posedge clk) (A != B) |-> (EQ == 1'b0)
    );

    // A high EQ must only occur for equal inputs.
    check_eq_high_implies_equal: assert property (
        @(posedge clk) (EQ == 1'b1) |-> (A == B)
    );

    // A low EQ must only occur for different inputs.
    check_eq_low_implies_different: assert property (
        @(posedge clk) (EQ == 1'b0) |-> (A != B)
    );

endmodule