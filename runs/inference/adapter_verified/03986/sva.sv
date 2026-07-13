module simple_adder_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

// Reset clears C on the next clock.
    check_reset_clears_c: assert property (
        @(posedge clk) rst |=> (C == 8'h00)
    );

// With reset low, C captures A + B on the next clock.
    check_addition_update: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (C == ($past(A) + $past(B)))
    );

// When A is zero, C captures B on the next clock.
    check_zero_a_passthrough: assert property (
        @(posedge clk) disable iff (rst) (A == 8'h00) |=> (C == $past(B))
    );

// When B is zero, C captures A on the next clock.
    check_zero_b_passthrough: assert property (
        @(posedge clk) disable iff (rst) (B == 8'h00) |=> (C == $past(A))
    );

// When A and B are equal, C captures A + B with no carry.
    check_equal_operands_no_carry: assert property (
        @(posedge clk) disable iff (rst) (A == B) |=> (C == ($past(A) + $past(B)))
    );

// When A is 8'hFF and B is 1, C wraps to 0 on the next clock.
    check_ff_plus_one_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst) ((A == 8'hFF) && (B == 8'h01)) |=> (C == 8'h00)
    );

endmodule
