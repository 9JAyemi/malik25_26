module my_module_sva (
    input logic clk,
    input logic i_0r0,
    input logic i_0r1,
    input logic i_0a,
    input logic o_0r0,
    input logic o_0r1,
    input logic o_0a,
    input logic reset
);

    // o_0r0 is i_0r0 gated by the inverse of o_0a.
    check_o0r0_gate: assert property (
        @(posedge clk) disable iff (reset)
        o_0r0 == (i_0r0 & ~o_0a)
    );

    // o_0r1 is i_0r1 gated by the inverse of o_0a.
    check_o0r1_gate: assert property (
        @(posedge clk) disable iff (reset)
        o_0r1 == (i_0r1 & ~o_0a)
    );

    // i_0a is the OR of the two output request signals.
    check_i0a_from_outputs: assert property (
        @(posedge clk) disable iff (reset)
        i_0a == (o_0r0 | o_0r1)
    );

    // i_0a equals the gated OR of the two input request signals.
    check_i0a_from_inputs: assert property (
        @(posedge clk) disable iff (reset)
        i_0a == ((i_0r0 | i_0r1) & ~o_0a)
    );

    // o_0a high blocks o_0r0.
    check_o0a_blocks_o0r0: assert property (
        @(posedge clk) disable iff (reset)
        o_0a |-> !o_0r0
    );

    // o_0a high blocks o_0r1.
    check_o0a_blocks_o0r1: assert property (
        @(posedge clk) disable iff (reset)
        o_0a |-> !o_0r1
    );

    // o_0a high blocks i_0a.
    check_o0a_blocks_i0a: assert property (
        @(posedge clk) disable iff (reset)
        o_0a |-> !i_0a
    );

    // o_0r0 can only be high when i_0r0 is high and o_0a is low.
    check_o0r0_source_conditions: assert property (
        @(posedge clk) disable iff (reset)
        o_0r0 |-> (i_0r0 && !o_0a)
    );

    // o_0r1 can only be high when i_0r1 is high and o_0a is low.
    check_o0r1_source_conditions: assert property (
        @(posedge clk) disable iff (reset)
        o_0r1 |-> (i_0r1 && !o_0a)
    );

    // Any asserted output request drives i_0a high.
    check_output_request_sets_i0a: assert property (
        @(posedge clk) disable iff (reset)
        (o_0r0 || o_0r1) |-> i_0a
    );

endmodule