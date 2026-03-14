module div8_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] wa,
    input logic [7:0] wb,
    input logic [7:0] result,
    input logic [7:0] wresult
);

    // If b is zero, both outputs are driven to 0.
    check_b_zero_outputs_zero: assert property (
        @(posedge clk) (b == 8'd0) |-> (result == 8'd0) && (wresult == 8'd0)
    );

    // If a and b are non-zero, result equals a / b.
    check_result_div_when_a_b_nonzero: assert property (
        @(posedge clk) (a != 8'd0) && (b != 8'd0) |-> (result == (a / b))
    );

    // If a and b are non-zero and wb is non-zero, wresult equals wa / wb.
    check_wresult_div_when_branch_and_wb_nonzero: assert property (
        @(posedge clk) (a != 8'd0) && (b != 8'd0) && (wb != 8'd0) |-> (wresult == (wa / wb))
    );

    // If a is zero and b is non-zero, both outputs are 0xFF.
    check_a_zero_b_nonzero_outputs_ff: assert property (
        @(posedge clk) (a == 8'd0) && (b != 8'd0) |-> (result == 8'hFF) && (wresult == 8'hFF)
    );

    // If b == 1 and a is non-zero, result equals a.
    check_result_identity_when_b_eq_1: assert property (
        @(posedge clk) (b == 8'd1) && (a != 8'd0) |-> (result == a)
    );

    // If a == b and both are non-zero, result equals 1.
    check_result_one_when_a_eq_b_nonzero: assert property (
        @(posedge clk) (a == b) && (a != 8'd0) |-> (result == 8'd1)
    );

    // If a < b with both non-zero, result equals 0 (integer division).
    check_result_zero_when_a_lt_b_nonzero: assert property (
        @(posedge clk) (a != 8'd0) && (b != 8'd0) && (a < b) |-> (result == 8'd0)
    );

    // If wb == 1 and branch a!=0 && b!=0 is taken, wresult equals wa.
    check_wresult_identity_when_wb_eq_1: assert property (
        @(posedge clk) (a != 8'd0) && (b != 8'd0) && (wb == 8'd1) |-> (wresult == wa)
    );

endmodule