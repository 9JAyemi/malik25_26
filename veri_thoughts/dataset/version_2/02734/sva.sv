module multi_input_output_sva (
    input logic [3:0] input1,
    input logic [1:0] input2,
    input logic input3,
    input logic input4,
    input logic input5,
    input logic input6,
    input logic input7,
    input logic input8,
    input logic output1
);
    // No clock/reset in RTL; combinational logic. Sample assertions on posedge of input3.

    // Output must equal the RTL's priority function.
    check_output1_function_equivalence: assert property (
        @(posedge input3)
            output1 == (
                ((input1 >= 4'b0110) && (input2 == 2'b10)) ||
                ( !((input1 >= 4'b0110) && (input2 == 2'b10)) &&
                  !(input3 && !input4) &&
                  (input5 && input6 && input7 && input8) )
            )
    );

    // If first condition holds, output1 must be 1.
    check_first_condition_sets_one: assert property (
        @(posedge input3)
            ((input1 >= 4'b0110) && (input2 == 2'b10)) |-> (output1 == 1'b1)
    );

    // If first is false and second holds, output1 must be 0.
    check_second_condition_sets_zero_when_first_false: assert property (
        @(posedge input3)
            (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
             (input3 == 1'b1) && (input4 == 1'b0)) |-> (output1 == 1'b0)
    );

    // If first and second are false and third holds, output1 must be 1.
    check_third_condition_sets_one_when_higher_false: assert property (
        @(posedge input3)
            (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
             !((input3 == 1'b1) && (input4 == 1'b0)) &&
             (input5 && input6 && input7 && input8)) |-> (output1 == 1'b1)
    );

    // If none of the conditions hold, output1 must be 0.
    check_default_sets_zero: assert property (
        @(posedge input3)
            (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
             !((input3 == 1'b1) && (input4 == 1'b0)) &&
             !(input5 && input6 && input7 && input8)) |-> (output1 == 1'b0)
    );

    // If output1 is 1, it must be due to the first or third condition per priority.
    check_no_spurious_one: assert property (
        @(posedge input3)
            (output1 == 1'b1) |-> (
                ((input1 >= 4'b0110) && (input2 == 2'b10)) ||
                (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
                 !((input3 == 1'b1) && (input4 == 1'b0)) &&
                 (input5 && input6 && input7 && input8))
            )
    );

    // If output1 is 0, it must be due to the second condition or default case.
    check_no_spurious_zero: assert property (
        @(posedge input3)
            (output1 == 1'b0) |-> (
                (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
                 (input3 == 1'b1) && (input4 == 1'b0)) ||
                (!((input1 >= 4'b0110) && (input2 == 2'b10)) &&
                 !((input3 == 1'b1) && (input4 == 1'b0)) &&
                 !(input5 && input6 && input7 && input8))
            )
    );

endmodule