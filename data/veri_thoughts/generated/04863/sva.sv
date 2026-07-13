module adder_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic [7:0]  q
);

    // A reset sampled on a negedge forces q low by the next negedge.
    check_reset_clears_q: assert property (
        @(negedge clk) reset |=> (q == 8'h00)
    );

    // After a non-reset cycle, q matches the prior low-byte sum.
    check_capture_low_byte_sum: assert property (
        @(negedge clk) disable iff (reset)
        !$past(reset) |-> (q == ($past(in1[7:0]) + $past(in2[7:0])))
    );

    // The first non-reset cycle after reset still presents q as zero.
    check_post_reset_q_zero: assert property (
        @(negedge clk) disable iff (reset)
        $past(reset) |-> (q == 8'h00)
    );

    // Same low bytes on adjacent capture edges keep q unchanged next cycle.
    check_same_low_bytes_hold_q: assert property (
        @(negedge clk) disable iff (reset)
        (!$past(reset) &&
         (in1[7:0] == $past(in1[7:0])) &&
         (in2[7:0] == $past(in2[7:0]))) |=> (q == $past(q))
    );

    // A zero left operand passes the prior right low byte through to q.
    check_zero_left_operand_passthrough: assert property (
        @(negedge clk) disable iff (reset)
        (!$past(reset) && ($past(in1[7:0]) == 8'h00)) |-> (q == $past(in2[7:0]))
    );

    // A zero right operand passes the prior left low byte through to q.
    check_zero_right_operand_passthrough: assert property (
        @(negedge clk) disable iff (reset)
        (!$past(reset) && ($past(in2[7:0]) == 8'h00)) |-> (q == $past(in1[7:0]))
    );

    // A full 9-bit sum of 0x100 wraps to 0x00 in q.
    check_overflow_wraps_to_zero: assert property (
        @(negedge clk) disable iff (reset)
        (!$past(reset) &&
         (({1'b0, $past(in1[7:0])} + {1'b0, $past(in2[7:0])}) == 9'h100)) |-> (q == 8'h00)
    );

endmodule