module FSM_sva #(
    parameter n = 2,
    parameter m = 1
)(
    input logic [n-1:0] in,
    input logic [m-1:0] out,
    input logic clk,
    input logic rst
);

    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    localparam logic [1:0] I0 = 2'b00;
    localparam logic [1:0] I1 = 2'b01;
    localparam logic [1:0] I2 = 2'b10;
    localparam logic [1:0] I3 = 2'b11;

    localparam logic [0:0] O0 = 1'b0;
    localparam logic [0:0] O1 = 1'b1;

    // Reset forces the FSM into S0 and drives out low.
    check_reset_state: assert property (
        @(posedge clk) !rst |-> (state == S0) && (out == O0)
    );

    // S0 with I0 advances to S1 and holds out low.
    check_s0_i0_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && (in == I0) |=> ((state == S1) && (out == O0))
    );

    // S0 with I1 advances to S2 and drives out high.
    check_s0_i1_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && (in == I1) |=> ((state == S2) && (out == O1))
    );

    // S0 with I2 or I3 holds state and keeps out low.
    check_s0_default_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S0) && ((in == I2) || (in == I3)) |=> ((state == S0) && (out == O0))
    );

    // S1 with I0 advances to S2 and holds out low.
    check_s1_i0_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && (in == I0) |=> ((state == S2) && (out == O0))
    );

    // S1 with I1 advances to S3 and drives out high.
    check_s1_i1_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && (in == I1) |=> ((state == S3) && (out == O1))
    );

    // S1 with I2 or I3 holds state and keeps out low.
    check_s1_default_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S1) && ((in == I2) || (in == I3)) |=> ((state == S1) && (out == O0))
    );

    // S2 with I0 advances to S3 and holds out low.
    check_s2_i0_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && (in == I0) |=> ((state == S3) && (out == O0))
    );

    // S2 with I1 advances to S0 and drives out high.
    check_s2_i1_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && (in == I1) |=> ((state == S0) && (out == O1))
    );

    // S2 with I2 or I3 holds state and keeps out low.
    check_s2_default_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S2) && ((in == I2) || (in == I3)) |=> ((state == S2) && (out == O0))
    );

    // S3 with I0 advances to S0 and holds out low.
    check_s3_i0_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && (in == I0) |=> ((state == S0) && (out == O0))
    );

    // S3 with I1 advances to S1 and drives out high.
    check_s3_i1_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && (in == I1) |=> ((state == S1) && (out == O1))
    );

    // S3 with I2 or I3 holds state and keeps out low.
    check_s3_default_transition: assert property (
        @(posedge clk) disable iff (!rst)
        (state == S3) && ((in == I2) || (in == I3)) |=> ((state == S3) && (out == O0))
    );

endmodule