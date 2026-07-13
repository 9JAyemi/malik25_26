module binary_comparator_sva (
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic [3:0] larger_num,
    input logic [3:0] pipeline_reg1,
    input logic [3:0] pipeline_reg2
);
    // Note: No clock/reset in RTL; asynchronous staging + combinational compare. Assertions are sampled on any edge of larger_num bits.

    // larger_num must equal the max of pipeline_reg1 and pipeline_reg2 whenever it changes.
    check_output_is_max: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        larger_num == (pipeline_reg1 > pipeline_reg2 ? pipeline_reg1 : pipeline_reg2)
    );

    // If pipeline_reg1 > pipeline_reg2, larger_num must select pipeline_reg1 when it changes.
    check_select_reg1_when_greater: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (pipeline_reg1 > pipeline_reg2) |-> (larger_num == pipeline_reg1)
    );

    // If pipeline_reg1 <= pipeline_reg2, larger_num must select pipeline_reg2 when it changes.
    check_select_reg2_when_not_greater: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (pipeline_reg1 <= pipeline_reg2) |-> (larger_num == pipeline_reg2)
    );

    // Ties must be resolved in favor of pipeline_reg2 whenever larger_num changes.
    check_tie_prefers_reg2: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (pipeline_reg1 == pipeline_reg2) |-> (larger_num == pipeline_reg2)
    );

    // larger_num must equal either pipeline_reg1 or pipeline_reg2 on any change.
    check_output_is_one_of_inputs: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (larger_num == pipeline_reg1) || (larger_num == pipeline_reg2)
    );

    // If larger_num equals pipeline_reg1, then pipeline_reg1 must be >= pipeline_reg2.
    check_consistency_when_eq_reg1: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (larger_num == pipeline_reg1) |-> (pipeline_reg1 >= pipeline_reg2)
    );

    // If larger_num equals pipeline_reg2, then pipeline_reg2 must be >= pipeline_reg1.
    check_consistency_when_eq_reg2: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        (larger_num == pipeline_reg2) |-> (pipeline_reg2 >= pipeline_reg1)
    );

    // larger_num must be >= pipeline_reg1 whenever it changes.
    check_output_ge_reg1: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        larger_num >= pipeline_reg1
    );

    // larger_num must be >= pipeline_reg2 whenever it changes.
    check_output_ge_reg2: assert property (
        @(posedge larger_num[0] or negedge larger_num[0] or
          posedge larger_num[1] or negedge larger_num[1] or
          posedge larger_num[2] or negedge larger_num[2] or
          posedge larger_num[3] or negedge larger_num[3])
        larger_num >= pipeline_reg2
    );
endmodule