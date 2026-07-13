module math_ops_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] cos,
    input logic [1:0] one,
    input logic [1:0] s1,
    input logic [1:0] s2,
    input logic [1:0] s1_out,
    input logic [1:0] s2_out
);

// s1_out is the registered sum of x2 and x3.
    check_s1_out_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s1_out == ($past(x2) + $past(x3)))
    );

// s2_out is the registered sum of x6 and x7.
    check_s2_out_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s2_out == ($past(x6) + $past(x7)))
    );

// x2 is the registered product of add1 and s2.
    check_x2_product: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (x2 == ($past(add1) * $past(s2)))
    );

// x3 is the registered product of cos and s1.
    check_x3_product: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (x3 == ($past(cos) * $past(s1)))
    );

// x6 is the registered product of sub5 and s1.
    check_x6_product: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (x6 == ($past(sub5) * $past(s1)))
    );

// x7 is the registered product of cos and s2.
    check_x7_product: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (x7 == ($past(cos) * $past(s2)))
    );

// add1 is the registered sum of cos and one.
    check_add1_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (add1 == ($past(cos) + $past(one)))
    );

// sub5 is the registered difference of one and cos.
    check_sub5_difference: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (sub5 == ($past(one) - $past(cos)))
    );

endmodule
