module bitwise_or_sva (
    input logic clock,
    input logic [`BITS-1:0] a_in,
    input logic [`BITS-1:0] b_in,
    output logic [`BITS-1:0] out
);
    // The output should always be the bitwise OR of a_in and b_in.
    bitwise_or_check: assert property (
        @(posedge clock) out == (a_in | b_in)
    );
endmodule