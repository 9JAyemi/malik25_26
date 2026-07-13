module comparator_sva #(
    parameter int n = 4
) (
    input logic         clk,
    input logic [n-1:0] in1,
    input logic [n-1:0] in2,
    input logic [1:0]   comp
);

    // comp is 01 when in1 is less than in2.
    check_less_than_encoding: assert property (
        @(posedge clk) (in1 < in2) |-> (comp == 2'b01)
    );

    // comp is 10 when in1 equals in2.
    check_equal_encoding: assert property (
        @(posedge clk) (in1 == in2) |-> (comp == 2'b10)
    );

    // comp is 10 when in1 is greater than in2.
    check_greater_than_encoding: assert property (
        @(posedge clk) (in1 > in2) |-> (comp == 2'b10)
    );

    // 01 only appears for the less-than case.
    check_01_implies_less_than: assert property (
        @(posedge clk) (comp == 2'b01) |-> (in1 < in2)
    );

    // 10 only appears when in1 is not less than in2.
    check_10_implies_not_less_than: assert property (
        @(posedge clk) (comp == 2'b10) |-> (in1 >= in2)
    );

    // comp never drives 00.
    check_comp_not_00: assert property (
        @(posedge clk) (comp != 2'b00)
    );

    // comp never drives 11.
    check_comp_not_11: assert property (
        @(posedge clk) (comp != 2'b11)
    );

    // comp matches the implemented comparator function.
    check_comp_function: assert property (
        @(posedge clk) comp == ((in1 < in2) ? 2'b01 : 2'b10)
    );

endmodule