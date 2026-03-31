module bitwise_operators_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] and_out,
    input logic [7:0] or_out,
    input logic [7:0] xor_out,
    input logic [7:0] not_out
);

// and_out must equal bitwise_and of a and b.
    check_and_function: assert property (
        @(posedge clk) and_out == (a & b)
    );

// or_out must equal bitwise_or of a and b.
    check_or_function: assert property (
        @(posedge clk) or_out == (a | b)
    );

// xor_out must equal bitwise_xor of a and b.
    check_xor_function: assert property (
        @(posedge clk) xor_out == (a ^ b)
    );

// not_out must equal bitwise_not of a.
    check_not_function: assert property (
        @(posedge clk) not_out == (~a)
    );

// and_out must be a subset of a.
    check_and_subset_a: assert property (
        @(posedge clk) (and_out & ~a) == 8'h00
    );

// and_out must be a subset of b.
    check_and_subset_b: assert property (
        @(posedge clk) (and_out & ~b) == 8'h00
    );

// or_out must contain a.
    check_or_superset_a: assert property (
        @(posedge clk) (or_out & ~a) == 8'h00
    );

// or_out must contain b.
    check_or_superset_b: assert property (
        @(posedge clk) (or_out & ~b) == 8'h00
    );

// xor_out must be disjoint from a.
    check_xor_disjoint_a: assert property (
        @(posedge clk) (xor_out & a) == 8'h00
    );

// xor_out must be disjoint from b.
    check_xor_disjoint_b: assert property (
        @(posedge clk) (xor_out & b) == 8'h00
    );

// not_out must be the bitwise complement of a.
    check_not_complement: assert property (
        @(posedge clk) (not_out & a) == 8'h00 && (not_out | a) == 8'hFF
    );

endmodule
