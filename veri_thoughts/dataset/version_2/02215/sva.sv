module comparator_generic_sva (
    input logic clk,
    input logic [3:0] Ain,
    input logic [3:0] Bin,
    input logic [3:0] CompOut
);
    // Bit3 is always 0.
    check_compout3_zero: assert property (
        @(posedge clk) (CompOut[3] == 1'b0)
    );

    // Exactly one of CompOut[2:0] is 1.
    check_compout_onehot_2_0: assert property (
        @(posedge clk) $onehot(CompOut[2:0])
    );

    // If Ain == Bin, CompOut encodes equals (0001).
    check_equal_drives_eq_code: assert property (
        @(posedge clk) (Ain == Bin) |-> (CompOut == 4'b0001)
    );

    // If Ain > Bin, CompOut encodes greater (0010).
    check_greater_drives_gt_code: assert property (
        @(posedge clk) (Ain > Bin) |-> (CompOut == 4'b0010)
    );

    // If Ain < Bin, CompOut encodes less (0100).
    check_less_drives_lt_code: assert property (
        @(posedge clk) (Ain < Bin) |-> (CompOut == 4'b0100)
    );

    // If CompOut[0] is 1, inputs must be equal.
    check_eq_code_means_equal: assert property (
        @(posedge clk) (CompOut[0] == 1'b1) |-> (Ain == Bin)
    );

    // If CompOut[1] is 1, Ain must be greater than Bin.
    check_gt_code_means_greater: assert property (
        @(posedge clk) (CompOut[1] == 1'b1) |-> (Ain > Bin)
    );

    // If CompOut[2] is 1, Ain must be less than Bin.
    check_lt_code_means_less: assert property (
        @(posedge clk) (CompOut[2] == 1'b1) |-> (Ain < Bin)
    );

    // Output remains stable when inputs are stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({Ain, Bin}) |-> $stable(CompOut)
    );
endmodule