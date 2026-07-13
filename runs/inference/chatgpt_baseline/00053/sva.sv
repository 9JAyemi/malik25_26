module adder_4bit_carry_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Outputs must match the full 5-bit addition result.
    check_full_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // No-overflow additions must produce no carry out.
    check_no_overflow_behavior: assert property (
        @(posedge clk)
        (({1'b0, a} + {1'b0, b} + cin) <= 5'd15)
        |-> ({1'b0, sum} == ({1'b0, a} + {1'b0, b} + cin) && cout == 1'b0)
    );

    // Overflow additions must wrap the low 4 bits and set carry out.
    check_overflow_behavior: assert property (
        @(posedge clk)
        (({1'b0, a} + {1'b0, b} + cin) >= 5'd16)
        |-> ({1'b0, sum} == (({1'b0, a} + {1'b0, b} + cin) - 5'd16) && cout == 1'b1)
    );

    // All-zero inputs must produce a zero result.
    check_zero_inputs: assert property (
        @(posedge clk)
        (a == 4'h0 && b == 4'h0 && cin == 1'b0)
        |-> (sum == 4'h0 && cout == 1'b0)
    );

    // Maximum inputs must produce 0xF with carry out set.
    check_max_inputs: assert property (
        @(posedge clk)
        (a == 4'hF && b == 4'hF && cin == 1'b1)
        |-> (sum == 4'hF && cout == 1'b1)
    );

endmodule