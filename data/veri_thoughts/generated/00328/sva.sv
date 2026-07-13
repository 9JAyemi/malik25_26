module priority_encoder_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] priority_output
);

    // priority_output matches the ternary max selection.
    check_priority_matches_ternary: assert property (
        @(posedge clk) priority_output == ((in1 > in2) ? in1 : in2)
    );

endmodule

module final_output_generator_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] final_output
);

    // final_output passes through in1 when the selected value is 4'b0001.
    check_final_output_case_0001: assert property (
        @(posedge clk) (((in1 > in2) ? in1 : in2) == 4'b0001) |-> (final_output == in1)
    );

    // final_output passes through in2 when the selected value is 4'b0010.
    check_final_output_case_0010: assert property (
        @(posedge clk) (((in1 > in2) ? in1 : in2) == 4'b0010) |-> (final_output == in2)
    );

    // final_output combines in1[3:1] with in2[0] when the selected value is 4'b0100.
    check_final_output_case_0100: assert property (
        @(posedge clk) (((in1 > in2) ? in1 : in2) == 4'b0100) |-> (final_output == {in1[3:1], in2[0]})
    );

    // final_output combines in2[3:1] with in1[0] when the selected value is 4'b1000.
    check_final_output_case_1000: assert property (
        @(posedge clk) (((in1 > in2) ? in1 : in2) == 4'b1000) |-> (final_output == {in2[3:1], in1[0]})
    );

    // final_output is zero for all other selected values.
    check_final_output_default_zero: assert property (
        @(posedge clk)
        (((in1 > in2) ? in1 : in2) != 4'b0001 &&
         ((in1 > in2) ? in1 : in2) != 4'b0010 &&
         ((in1 > in2) ? in1 : in2) != 4'b0100 &&
         ((in1 > in2) ? in1 : in2) != 4'b1000) |-> (final_output == 4'b0000)
    );

endmodule