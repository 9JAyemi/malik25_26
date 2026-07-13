module math_ops_sva #(
    parameter BITS = 2
) (
    input logic clk,
    input logic reset,
    input logic [1:0] cos,
    input logic [1:0] one,
    input logic [1:0] s1,
    input logic [1:0] s2,
    input logic [1:0] s1_out,
    input logic [1:0] s2_out
);

    // s1_out is the registered sum of the two multipliers.
    check_s1_out_registered_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s1_out == $past({
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s2)),
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s1))
        }))
    );

    // s2_out is the registered sum of the two multipliers.
    check_s2_out_registered_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s2_out == $past({
            ({2{1'b0}}} + ({2{1'b0}}} + $past(one)) * $past(s1)),
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s2))
        }))
    );

    // s1_out matches the RTL's full combinational equation.
    check_s1_out_full_equation: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s1_out == $past({
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s2)),
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s1))
        }))
    );

    // s2_out matches the RTL's full combinational equation.
    check_s2_out_full_equation: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s2_out == $past({
            ({2{1'b0}}} + ({2{1'b0}}} + $past(one)) * $past(s1)),
            ({2{1'b0}}} + ({2{1'b0}}} + $past(cos)) * $past(s2))
        }))
    );

endmodule