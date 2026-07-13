module lab5_2_1_sva(
    input logic in,
    input logic reset,
    input logic clk,
    input logic z,
    input logic [1:0] state,
    input logic [1:0] nextstate
);
    localparam logic [1:0] S0 = 2'd0;
    localparam logic [1:0] S1 = 2'd1;
    localparam logic [1:0] S2 = 2'd2;
    localparam logic [1:0] S3 = 2'd3;

    // A sampled high reset forces the FSM state to S0 by the next clock sample.
    check_reset_recovers_to_s0: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) === 1'b1) |-> (state === S0)
    );

    // State S0 drives z low.
    check_z_low_in_s0: assert property (
        @(posedge clk) disable iff (reset)
        (state === S0) |-> (z === 1'b0)
    );

    // State S1 drives z low.
    check_z_low_in_s1: assert property (
        @(posedge clk) disable iff (reset)
        (state === S1) |-> (z === 1'b0)
    );

    // State S2 drives z low.
    check_z_low_in_s2: assert property (
        @(posedge clk) disable iff (reset)
        (state === S2) |-> (z === 1'b0)
    );

    // State S3 drives z high.
    check_z_high_in_s3: assert property (
        @(posedge clk) disable iff (reset)
        (state === S3) |-> (z === 1'b1)
    );

    // In S0, input 1 selects S1.
    check_nextstate_s0_on_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S0) && (in === 1'b1)) |-> (nextstate === S1)
    );

    // In S0, input other than 1 holds S0.
    check_nextstate_s0_on_not_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S0) && (in !== 1'b1)) |-> (nextstate === S0)
    );

    // In S1, input 1 selects S2.
    check_nextstate_s1_on_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S1) && (in === 1'b1)) |-> (nextstate === S2)
    );

    // In S1, input other than 1 holds S1.
    check_nextstate_s1_on_not_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S1) && (in !== 1'b1)) |-> (nextstate === S1)
    );

    // In S2, input 1 selects S3.
    check_nextstate_s2_on_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S2) && (in === 1'b1)) |-> (nextstate === S3)
    );

    // In S2, input other than 1 holds S2.
    check_nextstate_s2_on_not_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S2) && (in !== 1'b1)) |-> (nextstate === S2)
    );

    // In S3, input 1 selects S1.
    check_nextstate_s3_on_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S3) && (in === 1'b1)) |-> (nextstate === S1)
    );

    // In S3, input other than 1 holds S3.
    check_nextstate_s3_on_not_one: assert property (
        @(posedge clk) disable iff (reset)
        ((state === S3) && (in !== 1'b1)) |-> (nextstate === S3)
    );

endmodule