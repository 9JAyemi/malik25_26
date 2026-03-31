module FSM_sva (
    input logic [1:0] in,
    input logic [0:0] out,
    input logic clk,
    input logic rst
);

// Reset drives the FSM to S0 and out to 0.
    check_reset_state: assert property (
        @(posedge clk) !rst |-> (state == S0) && (out == O0)
    );

// S0 with I0 advances to S1 and out remains 0.
    check_s0_i0_to_s1: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && (in == I0) |=> (state == S1) && (out == O0)
    );

// S0 with I1 advances to S2 and out becomes 1.
    check_s0_i1_to_s2: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && (in == I1) |=> (state == S2) && (out == O1)
    );

// S0 with I2/3 stays in S0 and out remains 0.
    check_s0_default_stays_s0: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && (in inside {I2, I3}) |=> (state == S0) && (out == O0)
    );

// S1 with I0 advances to S2 and out remains 0.
    check_s1_i0_to_s2: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && (in == I0) |=> (state == S2) && (out == O0)
    );

// S1 with I1 advances to S3 and out becomes 1.
    check_s1_i1_to_s3: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && (in == I1) |=> (state == S3) && (out == O1)
    );

// S1 with I2/3 stays in S1 and out remains 0.
    check_s1_default_stays_s1: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && (in inside {I2, I3}) |=> (state == S1) && (out == O0)
    );

// S2 with I0 advances to S3 and out remains 0.
    check_s2_i0_to_s3: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && (in == I0) |=> (state == S3) && (out == O0)
    );

// S2 with I1 advances to S0 and out becomes 1.
    check_s2_i1_to_s0: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && (in == I1) |=> (state == S0) && (out == O1)
    );

// S2 with I2/3 stays in S2 and out remains 0.
    check_s2_default_stays_s2: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && (in inside {I2, I3}) |=> (state == S2) && (out == O0)
    );

// S3 with I0 advances to S0 and out remains 0.
    check_s3_i0_to_s0: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && (in == I0) |=> (state == S0) && (out == O0)
    );

// S3 with I1 advances to S1 and out becomes 1.
    check_s3_i1_to_s1: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && (in == I1) |=> (state == S1) && (out == O1)
    );

// S3 with I2/3 stays in S3 and out remains 0.
    check_s3_default_stays_s3: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && (in inside {I2, I3}) |=> (state == S3) && (out == O0)
    );

endmodule
