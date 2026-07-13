module four_to_one_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out
);

    // All-zero inputs must drive out low.
    check_all_zero_drives_zero: assert property (
        @(posedge clk)
        ((in0 == 1'b0) && (in1 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0)) |-> (out == 1'b0)
    );

    // All-one inputs must drive out high.
    check_all_one_drives_one: assert property (
        @(posedge clk)
        ((in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1)) |-> (out == 1'b1)
    );

    // Any case that is not all ones must drive out low.
    check_not_all_one_drives_zero: assert property (
        @(posedge clk)
        (!((in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1))) |-> (out == 1'b0)
    );

    // Out can only be high when all inputs are high.
    check_out_high_only_when_all_high: assert property (
        @(posedge clk)
        (out == 1'b1) |-> ((in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1))
    );

    // Out must match the implemented four-input AND behavior.
    check_out_matches_function: assert property (
        @(posedge clk)
        (out == ((in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1)))
    );

endmodule