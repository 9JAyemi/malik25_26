module comparator_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [1:0] result
);
    // Result must be one of the three valid encodings.
    check_allowed_result_encoding: assert property (
        @(posedge clk) (result inside {2'b00, 2'b01, 2'b10})
    );

    // If in0 > in1 then result encodes greater-than (01).
    check_gt_implies_code: assert property (
        @(posedge clk) (in0 > in1) |-> (result == 2'b01)
    );

    // If in0 < in1 then result encodes less-than (10).
    check_lt_implies_code: assert property (
        @(posedge clk) (in0 < in1) |-> (result == 2'b10)
    );

    // If in0 == in1 then result encodes equal (00).
    check_eq_implies_code: assert property (
        @(posedge clk) (in0 == in1) |-> (result == 2'b00)
    );

    // If result encodes greater-than (01) then in0 > in1.
    check_code_implies_gt: assert property (
        @(posedge clk) (result == 2'b01) |-> (in0 > in1)
    );

    // If result encodes less-than (10) then in0 < in1.
    check_code_implies_lt: assert property (
        @(posedge clk) (result == 2'b10) |-> (in0 < in1)
    );

    // If result encodes equal (00) then in0 == in1.
    check_code_implies_eq: assert property (
        @(posedge clk) (result == 2'b00) |-> (in0 == in1)
    );

    // If inputs are unequal then result is not equal-code (00).
    check_inequality_implies_nonzero: assert property (
        @(posedge clk) (in0 != in1) |-> (result != 2'b00)
    );

    // If result is not equal-code (00) then inputs are unequal.
    check_nonzero_implies_inequality: assert property (
        @(posedge clk) (result != 2'b00) |-> (in0 != in1)
    );

    // If inputs hold their values, result must hold as well.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(in0) && $stable(in1)) |-> $stable(result)
    );
endmodule