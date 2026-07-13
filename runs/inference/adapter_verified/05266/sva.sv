module top_module_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] max
);

// max must equal the maximum of a, b, c, and d.
    check_max_of_four: assert property (
        @(posedge clk) max == max_of(a, b, c, d)
    );

// If a is the largest input, max must equal a.
    check_max_from_a: assert property (
        @(posedge clk) (a >= b) && (a >= c) && (a >= d) |-> (max == a)
    );

// If b is the largest input, max must equal b.
    check_max_from_b: assert property (
        @(posedge clk) (b >= a) && (b >= c) && (b >= d) |-> (max == b)
    );

// If c is the largest input, max must equal c.
    check_max_from_c: assert property (
        @(posedge clk) (c >= a) && (c >= b) && (c >= d) |-> (max == c)
    );

// If d is the largest input, max must equal d.
    check_max_from_d: assert property (
        @(posedge clk) (d >= a) && (d >= b) && (d >= c) |-> (max == d)
    );

endmodule
