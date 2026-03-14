module number_in_sva (
    input  logic [31:0] num_a,
    input  logic [31:0] num_b,
    input  logic [31:0] result,
    input  logic [4:0]  code,
    input  logic        btnm,
    input  logic [32:0] num_out
);
    // No clock/reset in RTL; assertions sample on posedge of btnm.
    // Combinational logic with internal latch-like state; num_out is 33-bit signed-magnitude of selected input.

    function automatic logic [31:0] abs32 (input logic [31:0] x);
        abs32 = x[31] ? ((~x) + 32'd1) : x;
    endfunction

    function automatic logic [32:0] fmt33 (input logic [31:0] x);
        fmt33 = x[31] ? {1'b1, ((~x) + 32'd1)} : {1'b0, x};
    endfunction

    ///// Output selection and formatting /////
    // num_out must equal the formatted value of one of {num_a,num_b,result}.
    check_num_out_matches_one_formatted_input: assert property (
        @(posedge btnm) (num_out == fmt33(num_a)) || (num_out == fmt33(num_b)) || (num_out == fmt33(result))
    );

    // If all inputs are equal, num_out equals the formatted value of that input.
    check_all_equal_drives_formatted_value: assert property (
        @(posedge btnm) (num_a == num_b) && (num_b == result) |-> (num_out == fmt33(num_a))
    );

    // The lower 32 bits of num_out equal the absolute value of one of the inputs.
    check_lower_bits_are_abs_of_some_input: assert property (
        @(posedge btnm) (num_out[31:0] == abs32(num_a)) || (num_out[31:0] == abs32(num_b)) || (num_out[31:0] == abs32(result))
    );

    ///// Sign-bit consistency /////
    // If num_out sign is 1, at least one input must be negative.
    check_sign_implies_some_input_negative: assert property (
        @(posedge btnm) num_out[32] |-> (num_a[31] || num_b[31] || result[31])
    );

    // If all inputs are non-negative, num_out sign must be 0.
    check_all_nonneg_implies_sign_zero: assert property (
        @(posedge btnm) (!num_a[31] && !num_b[31] && !result[31]) |-> (num_out[32] == 1'b0)
    );

    // If all inputs are negative, num_out sign must be 1.
    check_all_neg_implies_sign_one: assert property (
        @(posedge btnm) (num_a[31] && num_b[31] && result[31]) |-> (num_out[32] == 1'b1)
    );

    // If num_out sign is 0, its value must match some non-negative input exactly.
    check_sign_zero_matches_some_nonneg_input: assert property (
        @(posedge btnm) (num_out[32] == 1'b0) |-> 
            ( (!num_a[31] && (num_out[31:0] == num_a)) ||
              (!num_b[31] && (num_out[31:0] == num_b)) ||
              (!result[31] && (num_out[31:0] == result)) )
    );

    // If num_out sign is 1, its magnitude must match the abs() of some negative input.
    check_sign_one_matches_abs_of_some_negative_input: assert property (
        @(posedge btnm) (num_out[32] == 1'b1) |-> 
            ( (num_a[31] && (num_out[31:0] == abs32(num_a))) ||
              (num_b[31] && (num_out[31:0] == abs32(num_b))) ||
              (result[31] && (num_out[31:0] == abs32(result))) )
    );

    ///// Corner cases /////
    // If all inputs are zero, output must be zero-extended zero.
    check_all_zero_inputs_zero_output: assert property (
        @(posedge btnm) (num_a == 32'd0) && (num_b == 32'd0) && (result == 32'd0) |-> (num_out == 33'd0)
    );

    // If all inputs are INT_MIN, output must be sign=1 and magnitude=INT_MIN.
    check_all_minint_outputs_minint_magnitude: assert property (
        @(posedge btnm) (num_a == 32'h8000_0000) && (num_b == 32'h8000_0000) && (result == 32'h8000_0000)
            |-> (num_out == {1'b1, 32'h8000_0000})
    );

    // If all inputs share the same absolute value, num_out magnitude equals that common absolute value.
    check_common_abs_magnitude: assert property (
        @(posedge btnm) (abs32(num_a) == abs32(num_b)) && (abs32(num_b) == abs32(result))
            |-> (num_out[31:0] == abs32(num_a))
    );

endmodule