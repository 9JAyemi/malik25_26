module ALU_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [4:0]  CTRL,
    input logic [31:0] RES
);

    // RES is zero whenever reset is asserted.
    check_reset_clears_res: assert property (
        @(posedge clk) rst |-> (RES == 32'b0)
    );

    // Addition result is registered on the next clock.
    check_addition_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00000) |=> (RES == ($past(A) + $past(B)))
    );

    // Subtraction result is registered on the next clock.
    check_subtraction_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00001) |=> (RES == ($past(A) - $past(B)))
    );

    // Bitwise AND result is registered on the next clock.
    check_and_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00010) |=> (RES == ($past(A) & $past(B)))
    );

    // Bitwise OR result is registered on the next clock.
    check_or_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00011) |=> (RES == ($past(A) | $past(B)))
    );

    // Bitwise XOR result is registered on the next clock.
    check_xor_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00100) |=> (RES == ($past(A) ^ $past(B)))
    );

    // Logical left shift result is registered on the next clock.
    check_shift_left_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL == 5'b00101) |=> (RES == ($past(A) << $past(B)))
    );

    // Unsupported control values drive zero on the next clock.
    check_default_zero_result: assert property (
        @(posedge clk) disable iff (rst)
        (CTRL >= 5'b00110) |=> (RES == 32'b0)
    );

endmodule