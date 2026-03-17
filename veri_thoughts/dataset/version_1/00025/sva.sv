module pipelined_xor_gate_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out,
    input logic a_reg,
    input logic b_reg,
    input logic a_reg1,
    input logic b_reg1,
    input logic xor_out,
    input logic xor_out1
);

    // Stage 2 captures input a on the previous clock.
    check_stage2_capture_a: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (a_reg == $past(a))
    );

    // Stage 2 captures input b on the previous clock.
    check_stage2_capture_b: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (b_reg == $past(b))
    );

    // Stage 1 captures the previous value of a_reg.
    check_stage1_capture_a: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (a_reg1 == $past(a_reg))
    );

    // Stage 1 captures the previous value of b_reg.
    check_stage1_capture_b: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (b_reg1 == $past(b_reg))
    );

    // xor_out is the XOR of the stage 2 registers.
    check_stage2_xor_logic: assert property (
        @(posedge clk) (xor_out == (a_reg ^ b_reg))
    );

    // xor_out1 is the XOR of the stage 1 registers.
    check_stage1_xor_logic: assert property (
        @(posedge clk) (xor_out1 == (a_reg1 ^ b_reg1))
    );

    // The module output is directly driven by xor_out1.
    check_output_connection: assert property (
        @(posedge clk) (out == xor_out1)
    );

    // The stage 1 XOR is the previous cycle's stage 2 XOR.
    check_xor_pipeline_delay: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (xor_out1 == $past(xor_out))
    );

    // Equal inputs produce a low output two clocks later.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk) (a == b) |=> ##1 (out == 1'b0)
    );

    // Different inputs produce a high output two clocks later.
    check_different_inputs_drive_one: assert property (
        @(posedge clk) (a != b) |=> ##1 (out == 1'b1)
    );

    // After pipeline fill, out matches the XOR of inputs from two clocks earlier.
    check_output_two_cycle_latency: assert property (
        @(posedge clk) (!$initstate && !$past($initstate) && !$past($initstate, 2)) |-> (out == ($past(a, 2) ^ $past(b, 2)))
    );

endmodule