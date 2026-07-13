module top_module_sva (
    input  logic        clk,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic [7:0]  c,
    input  logic [7:0]  d,
    input  logic [7:0]  final_output
);
    // Local reference model of DUT behavior
    logic [10:0] sum_full;
    logic [7:0]  sum8;
    logic [7:0]  max1, max2, max3;
    logic [7:0]  model_final;
    logic [7:0]  sum_minus_a, sum_minus_b, sum_minus_c, sum_minus_d;
    logic [7:0]  final_plus_max;
    logic [9:0]  three_a_full;
    logic [7:0]  three_a;

    assign sum_full = a + b + c + d;
    assign sum8     = sum_full[7:0];

    assign max1 = (a > b) ? a : b;
    assign max2 = (c > d) ? c : d;
    assign max3 = (max1 > max2) ? max1 : max2;

    assign model_final  = sum8 - max3;
    assign sum_minus_a  = sum8 - a;
    assign sum_minus_b  = sum8 - b;
    assign sum_minus_c  = sum8 - c;
    assign sum_minus_d  = sum8 - d;
    assign final_plus_max = final_output + max3;

    assign three_a_full = a + a + a;
    assign three_a      = three_a_full[7:0];

    // final_output equals (a+b+c+d) - max(a,b,c,d) modulo 256
    check_final_output_sum_minus_max: assert property (
        @(posedge clk) final_output == model_final
    );

    // final_output + max(a,b,c,d) equals (a+b+c+d) modulo 256
    check_final_plus_max_equals_sum: assert property (
        @(posedge clk) final_plus_max == sum8
    );

    // If a is a maximum (ties allowed), final_output == sum - a (mod 256)
    check_subtract_a_when_a_is_max: assert property (
        @(posedge clk) ((a >= b) && (a >= c) && (a >= d)) |-> (final_output == sum_minus_a)
    );

    // If b is a maximum (ties allowed), final_output == sum - b (mod 256)
    check_subtract_b_when_b_is_max: assert property (
        @(posedge clk) ((b >= a) && (b >= c) && (b >= d)) |-> (final_output == sum_minus_b)
    );

    // If c is a maximum (ties allowed), final_output == sum - c (mod 256)
    check_subtract_c_when_c_is_max: assert property (
        @(posedge clk) ((c >= a) && (c >= b) && (c >= d)) |-> (final_output == sum_minus_c)
    );

    // If d is a maximum (ties allowed), final_output == sum - d (mod 256)
    check_subtract_d_when_d_is_max: assert property (
        @(posedge clk) ((d >= a) && (d >= b) && (d >= c)) |-> (final_output == sum_minus_d)
    );

    // If all inputs are equal, final_output equals 3*a modulo 256
    check_all_equal_inputs: assert property (
        @(posedge clk) ((a == b) && (b == c) && (c == d)) |-> (final_output == three_a)
    );

    // If all inputs are zero, final_output must be zero
    check_all_zero_inputs: assert property (
        @(posedge clk) ((a == 8'h00) && (b == 8'h00) && (c == 8'h00) && (d == 8'h00)) |-> (final_output == 8'h00)
    );

    // final_output equals sum minus one of the maximal inputs (ties allowed)
    check_subtract_one_of_maxima: assert property (
        @(posedge clk)
            ( ((a >= b) && (a >= c) && (a >= d) && (final_output == sum_minus_a)) ||
              ((b >= a) && (b >= c) && (b >= d) && (final_output == sum_minus_b)) ||
              ((c >= a) && (c >= b) && (c >= d) && (final_output == sum_minus_c)) ||
              ((d >= a) && (d >= b) && (d >= c) && (final_output == sum_minus_d)) )
    );

    // If the maximum value is zero, final_output equals sum (no subtraction effect)
    check_max_zero_no_effect: assert property (
        @(posedge clk) (max3 == 8'h00) |-> (final_output == sum8)
    );

endmodule