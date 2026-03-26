module multi_input_module_sva(
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic input5,
    input logic input6,
    input logic input7,
    input logic input8,
    input logic output1
);

    // output1 is high whenever input1 is high.
    check_output_high_when_input1_high: assert property (
        @($global_clock) input1 |-> output1
    );

    // output1 is low when input1 is low and input2 is high.
    check_output_low_when_input1_low_and_input2_high: assert property (
        @($global_clock) (!input1 && input2) |-> !output1
    );

    // output1 is low when input1 and input2 are low and input3-input8 are all low.
    check_output_low_when_all_secondary_inputs_low: assert property (
        @($global_clock)
        (!input1 && !input2 && !input3 && !input4 && !input5 && !input6 && !input7 && !input8)
        |-> !output1
    );

    // output1 is high when input1 and input2 are low and any of input3-input8 is high.
    check_output_high_when_any_secondary_input_high: assert property (
        @($global_clock)
        (!input1 && !input2 && (input3 || input4 || input5 || input6 || input7 || input8))
        |-> output1
    );

    // output1 matches the complete combinational function implemented by the RTL.
    check_output_matches_rtl_function: assert property (
        @($global_clock)
        output1 == (input1 ? 1'b1 : (input2 ? 1'b0 : (input3 || input4 || input5 || input6 || input7 || input8)))
    );

endmodule