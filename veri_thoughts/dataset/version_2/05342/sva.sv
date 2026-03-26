module top_module_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic [3:0] max_out
);

    // out is the 4-bit sum of in1 and in2.
    check_out_matches_sum: assert property (
        @(posedge clk) out == (in1 + in2)
    );

    // max_out follows the RTL max expression using out and the sum.
    check_max_out_matches_rtl_max_expr: assert property (
        @(posedge clk) max_out == ((out > (in1 + in2)) ? out : (in1 + in2))
    );

    // Since out is assigned from the sum, max_out must equal out.
    check_max_out_equals_out: assert property (
        @(posedge clk) max_out == out
    );

    // max_out also equals the computed 4-bit sum.
    check_max_out_matches_sum: assert property (
        @(posedge clk) max_out == (in1 + in2)
    );

endmodule