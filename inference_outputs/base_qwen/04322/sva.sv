module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic greater,
    input logic less
);
    // greater should be HIGH when A is greater than B
    greater_check: assert property (
        @(posedge clk) disable iff (!reset_n) (A > B) |-> greater
    );

    // less should be HIGH when A is less than B
    less_check: assert property (
        @(posedge clk) disable iff (!reset_n) (A < B) |-> less
    );

    // greater and less should not be HIGH at the same time
    exclusive_check: assert property (
        @(posedge clk) disable iff (!reset_n) !(greater && less)
    );

    // greater and less should be LOW when A is equal to B
    equal_check: assert property (
        @(posedge clk) disable iff (!reset_n) (A == B) |-> !(greater || less)
    );
endmodule