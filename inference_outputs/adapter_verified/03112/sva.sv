module adder_4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] s,
    input logic cout
);

// Sum must match the 5-bit addition of a, b, and cin.
    check_full_sum: assert property (
        @(posedge clk) {cout, s} == ({1'b0, a} + {1'b0, b} + cin)
    );

// s must match the lower 4 bits of the addition result.
    check_sum_bits: assert property (
        @(posedge clk) s == (({1'b0, a} + {1'b0, b} + cin) & 4'hF)
    );

// cout must match the carry-out bit of the addition.
    check_carry_out: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) > 5'd15)
    );

// Zero inputs must produce a zero sum and no carry.
    check_zero_case: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b0) |-> (s == 4'h0 && cout == 1'b0)
    );

// Maximum inputs must produce 4'hF with carry-out asserted.
    check_max_case: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> (s == 4'hF && cout == 1'b1)
    );

endmodule
