module Comparator_sva #(
    parameter int n = 4
)(
    input logic clk,
    input logic [n-1:0] in1,
    input logic [n-1:0] in2,
    input logic [1:0] out
);

    // If in1 > in2, out must be 01.
    check_out_is_01_when_gt: assert property (
        @(posedge clk) (in1 > in2) |=> (out == 2'b01)
    );

    // If in1 == in2, out must be 00.
    check_out_is_00_when_eq: assert property (
        @(posedge clk) (in1 == in2) |=> (out == 2'b00)
    );

    // If in1 < in2, out must be 10.
    check_out_is_10_when_lt: assert property (
        @(posedge clk) (in1 < in2) |=> (out == 2'b10)
    );

    // out must never be 11.
    check_out_never_11: assert property (
        @(posedge clk) !(out == 2'b11)
    );

    // If out is 01, then in1 > in2.
    check_out_01_implies_gt: assert property (
        @(posedge clk) (out == 2'b01) |=> (in1 > in2)
    );

    // If out is 00, then in1 == in2.
    check_out_00_implies_eq: assert property (
        @(posedge clk) (out == 2'b00) |=> (in1 == in2)
    );

    // If out is 10, then in1 < in2.
    check_out_10_implies_lt: assert property (
        @(posedge clk) (out == 2'b10) |=> (in1 < in2)
    );

    // out[0] reflects (in1 > in2).
    check_bit0_matches_gt: assert property (
        @(posedge clk) out[0] == (in1 > in2)
    );

    // out[1] reflects (in1 < in2).
    check_bit1_matches_lt: assert property (
        @(posedge clk) out[1] == (in1 < in2)
    );

    // If inputs are stable across cycles, output is stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2)) |=> $stable(out)
    );

endmodule