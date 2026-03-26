module my_module_sva (
    input logic clk,
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

    // First branch forces output1 high.
    check_first_branch_sets_high: assert property (
        @(posedge clk) (input1 && input2) |-> (output1 == 1'b1)
    );

    // Second branch forces output1 low when the first branch is not taken.
    check_second_branch_sets_low: assert property (
        @(posedge clk) (!(input1 && input2) && !input3 && !input4) |-> (output1 == 1'b0)
    );

    // Third branch forces output1 high when higher-priority branches are not taken.
    check_third_branch_sets_high: assert property (
        @(posedge clk) (!(input1 && input2) && (input3 || input4) && input5 && input6 && input7) |-> (output1 == 1'b1)
    );

    // Default branch passes input8 when no earlier branch matches.
    check_default_branch_follows_input8: assert property (
        @(posedge clk) (!(input1 && input2) && (input3 || input4) && !(input5 && input6 && input7)) |-> (output1 == input8)
    );

    // output1 matches the full priority-ordered combinational function.
    check_full_priority_function: assert property (
        @(posedge clk)
        output1 == ((input1 && input2) ? 1'b1 :
                    ((!input3 && !input4) ? 1'b0 :
                    ((input5 && input6 && input7) ? 1'b1 : input8)))
    );

endmodule