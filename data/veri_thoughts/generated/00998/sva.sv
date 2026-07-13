module custom_module_sva (
    input logic input_1,
    input logic input_2,
    input logic input_3,
    input logic input_4,
    input logic input_5,
    input logic input_6,
    input logic input_7,
    input logic input_8,
    input logic input_9,
    input logic input_10,
    input logic output_1
);
    // No explicit clock/reset in DUT; pure combinational; sample on any input edge.

    // If any condition is true, output_1 must be 1.
    check_any_condition_sets_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        ( input_1 ||
          (input_2 && input_3) ||
          input_4 ||
          input_5 ||
          (input_6 && input_7 && input_8) ||
          (input_9 && input_10) ) |-> (output_1 == 1'b1)
    );

    // input_1 alone drives output_1 high.
    check_input1_sets_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        input_1 |-> (output_1 == 1'b1)
    );

    // input_2 & input_3 drive output_1 high.
    check_input2_and_input3_set_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        (input_2 && input_3) |-> (output_1 == 1'b1)
    );

    // input_4 alone drives output_1 high.
    check_input4_sets_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        input_4 |-> (output_1 == 1'b1)
    );

    // input_5 alone drives output_1 high.
    check_input5_sets_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        input_5 |-> (output_1 == 1'b1)
    );

    // input_6 & input_7 & input_8 drive output_1 high.
    check_input6_7_8_set_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        (input_6 && input_7 && input_8) |-> (output_1 == 1'b1)
    );

    // input_9 & input_10 drive output_1 high.
    check_input9_10_set_output_high: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        (input_9 && input_10) |-> (output_1 == 1'b1)
    );

    // If output_1 is high, at least one condition must be true.
    check_output_high_implies_some_condition: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        (output_1 == 1'b1) |-> ( input_1 ||
                                 (input_2 && input_3) ||
                                 input_4 ||
                                 input_5 ||
                                 (input_6 && input_7 && input_8) ||
                                 (input_9 && input_10) )
    );

    // If no condition is true, output_1 must be low.
    check_no_conditions_implies_output_low: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        ( !input_1 &&
          !(input_2 && input_3) &&
          !input_4 &&
          !input_5 &&
          !(input_6 && input_7 && input_8) &&
          !(input_9 && input_10) ) |-> (output_1 == 1'b0)
    );

    // If output_1 is low, no condition should be true.
    check_output_low_implies_no_conditions: assert property (
        @(posedge input_1 or negedge input_1 or
          posedge input_2 or negedge input_2 or
          posedge input_3 or negedge input_3 or
          posedge input_4 or negedge input_4 or
          posedge input_5 or negedge input_5 or
          posedge input_6 or negedge input_6 or
          posedge input_7 or negedge input_7 or
          posedge input_8 or negedge input_8 or
          posedge input_9 or negedge input_9 or
          posedge input_10 or negedge input_10)
        (output_1 == 1'b0) |-> ( !input_1 &&
                                 !(input_2 && input_3) &&
                                 !input_4 &&
                                 !input_5 &&
                                 !(input_6 && input_7 && input_8) &&
                                 !(input_9 && input_10) )
    );

endmodule