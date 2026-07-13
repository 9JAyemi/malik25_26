module bitwise_or_sva (
    input logic clock,
    input logic [`BITS-1:0] a_in,
    input logic [`BITS-1:0] b_in,
    input logic [`BITS-1:0] out
);

    // out equals the previous cycle's bitwise OR of a_in and b_in.
    check_out_matches_previous_or: assert property (
        @(posedge clock) 1'b1 |=> (out == ($past(a_in) | $past(b_in)))
    );

    // out is never less than the previous cycle's a_in.
    check_out_ge_previous_a: assert property (
        @(posedge clock) 1'b1 |=> (out >= $past(a_in))
    );

    // out is never less than the previous cycle's b_in.
    check_out_ge_previous_b: assert property (
        @(posedge clock) 1'b1 |=> (out >= $past(b_in))
    );

    // out is never less than the bitwise OR of the previous cycle's inputs.
    check_out_ge_previous_or: assert property (
        @(posedge clock) 1'b1 |=> (out >= ($past(a_in) | $past(b_in)))
    );

    // out is never greater than the previous cycle's a_in.
    check_out_le_previous_a: assert property (
        @(posedge clock) 1'b1 |=> (out <= $past(a_in))
    );

    // out is never greater than the previous cycle's b_in.
    check_out_le_previous_b: assert property (
        @(posedge clock) 1'b1 |=> (out <= $past(b_in))
    );

    // out is never greater than the bitwise OR of the previous cycle's inputs.
    check_out_le_previous_or: assert property (
        @(posedge clock) 1'b1 |=> (out <= ($past(a_in) | $past(b_in)))
    );

endmodule