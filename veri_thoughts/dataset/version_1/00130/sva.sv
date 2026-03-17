module incrementer_assertions (
    input logic clk,
    input logic signed [31:0] in,
    input logic signed [31:0] out
);

    // Out is the previous cycle's input incremented by one.
    check_registered_increment: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(in) + 32'sd1))
    );

    // Zero increments to one on the next clock.
    check_zero_to_one: assert property (
        @(posedge clk) (in == 32'sd0) |=> (out == 32'sd1)
    );

    // Minus one increments to zero on the next clock.
    check_minus_one_to_zero: assert property (
        @(posedge clk) (in == -32'sd1) |=> (out == 32'sd0)
    );

    // Maximum positive value wraps to minimum negative on the next clock.
    check_positive_overflow_wrap: assert property (
        @(posedge clk) (in == 32'sh7fffffff) |=> (out == 32'sh80000000)
    );

    // Minimum negative value increments to the next signed value.
    check_negative_min_to_next: assert property (
        @(posedge clk) (in == 32'sh80000000) |=> (out == 32'sh80000001)
    );

endmodule