module bitwise_or_sva (
    input logic clock,
    input logic [`BITS-1:0] a_in,
    input logic [`BITS-1:0] b_in,
    input logic [`BITS-1:0] out
);

// Next-cycle out equals bitwise OR of current a_in and b_in.
    check_next_cycle_or_function: assert property (
        @(posedge clock) 1'b1 |=> (out == ($past(a_in) | $past(b_in)))
    );

// If a_in is all zeros, next-cycle out equals current b_in.
    check_zero_a_passthrough: assert property (
        @(posedge clock) (a_in == 8'h00) |=> (out == $past(b_in))
    );

// If b_in is all zeros, next-cycle out equals current a_in.
    check_zero_b_passthrough: assert property (
        @(posedge clock) (b_in == 8'h00) |=> (out == $past(a_in))
    );

// If both inputs are all ones, next-cycle out is all ones.
    check_all_ones_result: assert property (
        @(posedge clock) ((a_in == 8'hFF) && (b_in == 8'hFF)) |=> (out == 8'hFF)
    );

// If both inputs are all zeros, next-cycle out is all zeros.
    check_all_zeros_result: assert property (
        @(posedge clock) ((a_in == 8'h00) && (b_in == 8'h00)) |=> (out == 8'h00)
    );

// If a_in equals current out, next-cycle out equals current b_in.
    check_a_matches_out_implies_b_passthrough: assert property (
        @(posedge clock) (a_in == out) |=> (out == $past(b_in))
    );

// If b_in equals current out, next-cycle out equals current a_in.
    check_b_matches_out_implies_a_passthrough: assert property (
        @(posedge clock) (b_in == out) |=> (out == $past(a_in))
    );

endmodule
