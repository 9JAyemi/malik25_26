module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] S,
    input logic D,
    input logic [3:0] B
);

    // RTL is combinational; clk is an external sampling clock.
    // There is no reset in the DUT.

    // S=00 passes A directly to B.
    check_passthrough_when_s0: assert property (
        @(posedge clk)
        (S == 2'b00) |-> (B == A)
    );

    // D=1 and S=01 rotate then shift right by 1.
    check_right_path_when_s1: assert property (
        @(posedge clk)
        ((D == 1'b1) && (S == 2'b01)) |-> (B == {1'b0, A[2:0]})
    );

    // D=1 and S=10 rotate then shift right by 2.
    check_right_path_when_s2: assert property (
        @(posedge clk)
        ((D == 1'b1) && (S == 2'b10)) |-> (B == {2'b00, A[1:0]})
    );

    // D=1 and S=11 rotate then shift right by 3.
    check_right_path_when_s3: assert property (
        @(posedge clk)
        ((D == 1'b1) && (S == 2'b11)) |-> (B == {3'b000, A[0]})
    );

    // D=0 and S=01 rotate then shift left by 1.
    check_left_path_when_s1: assert property (
        @(posedge clk)
        ((D == 1'b0) && (S == 2'b01)) |-> (B == {A[1:0], A[3], 1'b0})
    );

    // D=0 and S=10 rotate then shift left by 2.
    check_left_path_when_s2: assert property (
        @(posedge clk)
        ((D == 1'b0) && (S == 2'b10)) |-> (B == {A[3:2], 2'b00})
    );

    // D=0 and S=11 rotate then shift left by 3.
    check_left_path_when_s3: assert property (
        @(posedge clk)
        ((D == 1'b0) && (S == 2'b11)) |-> (B == {A[1], 3'b000})
    );

endmodule