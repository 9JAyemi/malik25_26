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

    // With reset low and OP high, the next output is A minus B.
    check_subtract_operation: assert property (
        @(posedge CLK) disable iff (RST) (OP == 1'b1) |=> (C == ($past(A) - $past(B)))
    );

    // With reset low and OP low, the next output is A plus B.
    check_add_operation: assert property (
        @(posedge CLK) disable iff (RST) (OP == 1'b0) |=> (C == ($past(A) + $past(B)))
    );

    // If reset stays asserted across consecutive clocks, the output remains zero.
    check_reset_holds_output_zero: assert property (
        @(posedge CLK) (RST && $past(RST)) |-> (C == 8'h00)
    );

    // If reset deasserts and both operands are zero, the output becomes zero on the next clock.
    check_zero_operands_after_reset: assert property (
        @(posedge CLK) ($fell(RST) && (A == 8'h00) && (B == 8'h00)) |=> (C == 8'h00)
    );

    // If reset deasserts and A is zero, the output becomes the negated B on the next clock.
    check_negate_b_after_reset: assert property (
        @(posedge CLK) ($fell(RST) && (A == 8'h00)) |=> (C == (~$past(B) + 8'h01))
    );

    // If reset deasserts and B is zero, the output becomes A on the next clock.
    check_passthrough_a_after_reset: assert property (
        @(posedge CLK) ($fell(RST) && (B == 8'h00)) |=> (C == $past(A))
    );

endmodule