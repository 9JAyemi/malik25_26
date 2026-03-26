module radix2_linediv_sva (
    input logic        clk,
    input logic [1:0]  iSOURCE_DIVIDEND,
    input logic [31:0] iSOURCE_DIVISOR,
    input logic [30:0] iSOURCE_R,
    input logic [1:0]  oOUT_DATA_Q,
    input logic [30:0] oOUT_DATA_R
);

    function automatic [31:0] func_radix2_linediv;
        input [31:0] func_dividend;
        input [31:0] func_divisor;
        reg [31:0] func_sub;
        begin
            func_sub = func_dividend + (~func_divisor + 32'h00000001);
            if (func_sub[31]) begin
                func_radix2_linediv = {1'b0, func_dividend[30:0]};
            end
            else begin
                func_radix2_linediv = {1'b1, func_sub[30:0]};
            end
        end
    endfunction

    // The upper quotient bit is the quotient result of the first divide step.
    check_first_stage_quotient_bit: assert property (
        @(posedge clk)
        oOUT_DATA_Q[1] ==
        (func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[31]
    );

    // The lower quotient bit and final remainder are the second divide step result.
    check_second_stage_qr_result: assert property (
        @(posedge clk)
        {oOUT_DATA_Q[0], oOUT_DATA_R} ==
        func_radix2_linediv(
            {(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]},
            iSOURCE_DIVISOR
        )
    );

    // The quotient output packs the first-step bit above the second-step bit.
    check_output_quotient_packing: assert property (
        @(posedge clk)
        oOUT_DATA_Q == {
            (func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[31],
            (func_radix2_linediv(
                {(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]},
                iSOURCE_DIVISOR
            ))[31]
        }
    );

    // A negative first-step subtraction forces the first quotient bit low.
    check_first_stage_negative_path: assert property (
        @(posedge clk)
        (({iSOURCE_R, iSOURCE_DIVIDEND[1]} + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b1)
        |-> (oOUT_DATA_Q[1] == 1'b0)
    );

    // A non-negative first-step subtraction forces the first quotient bit high.
    check_first_stage_nonnegative_path: assert property (
        @(posedge clk)
        (({iSOURCE_R, iSOURCE_DIVIDEND[1]} + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b0)
        |-> (oOUT_DATA_Q[1] == 1'b1)
    );

    // A negative second-step subtraction forces the second quotient bit low.
    check_second_stage_negative_path_q: assert property (
        @(posedge clk)
        (({(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]}
          + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b1)
        |-> (oOUT_DATA_Q[0] == 1'b0)
    );

    // A negative second-step subtraction keeps the shifted dividend bits as remainder.
    check_second_stage_negative_path_r: assert property (
        @(posedge clk)
        (({(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]}
          + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b1)
        |-> (oOUT_DATA_R ==
             {(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[29:0], iSOURCE_DIVIDEND[0]})
    );

    // A non-negative second-step subtraction forces the second quotient bit high.
    check_second_stage_nonnegative_path_q: assert property (
        @(posedge clk)
        (({(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]}
          + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b0)
        |-> (oOUT_DATA_Q[0] == 1'b1)
    );

    // A non-negative second-step subtraction drives the subtraction result as remainder.
    check_second_stage_nonnegative_path_r: assert property (
        @(posedge clk)
        (({(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]}
          + (~iSOURCE_DIVISOR + 32'h00000001))[31] == 1'b0)
        |-> (oOUT_DATA_R ==
             (({(func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR))[30:0], iSOURCE_DIVIDEND[0]}
               + (~iSOURCE_DIVISOR + 32'h00000001))[30:0]))
    );

endmodule