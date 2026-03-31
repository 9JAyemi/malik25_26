module simple_calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       OP,
    input logic       CLK,
    input logic       RST,
    input logic [7:0] C
);

    // Reset clears the registered output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge CLK) RST |=> (C == 8'h00)
    );

    // In add mode, the next output is the previous cycle's A+B.
    check_add_mode_result: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b0) |=> (C == ($past(A) + $past(B)))
    );

    // In subtract mode, the next output is the previous cycle's A-B.
    check_subtract_mode_result: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b1) |=> (C == ($past(A) - $past(B)))
    );

    // In add mode with equal operands, the next output is zero.
    check_add_equal_operands_zero: assert property (
        @(posedge CLK) disable iff (RST)
        ((OP == 1'b0) && (A == B)) |=> (C == 8'h00)
    );

    // In subtract mode with equal operands, the next output is zero.
    check_subtract_equal_operands_zero: assert property (
        @(posedge CLK) disable iff (RST)
        ((OP == 1'b1) && (A == B)) |=> (C == 8'h00)
    );

endmodule