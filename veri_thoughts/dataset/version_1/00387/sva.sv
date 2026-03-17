module FSM_assertions #(
    parameter n = 4,
    parameter m = 2
)(
    input logic [n-1:0] in,
    input logic [m-1:0] out,
    input logic clk,
    input logic [2:0] state,
    input logic [2:0] next_state
);

    localparam logic [2:0] S0 = 3'b000;
    localparam logic [2:0] S1 = 3'b001;
    localparam logic [2:0] S2 = 3'b010;
    localparam logic [2:0] S3 = 3'b011;
    localparam logic [2:0] S4 = 3'b100;
    localparam logic [2:0] S5 = 3'b101;
    localparam logic [2:0] S6 = 3'b110;
    localparam logic [2:0] S7 = 3'b111;

    // out[0] is high only in states S0 through S3.
    check_out0_logic: assert property (
        @(posedge clk)
        out[0] == ((state == S0) || (state == S1) || (state == S2) || (state == S3))
    );

    // out[1] is high only in states S4 through S7.
    check_out1_logic: assert property (
        @(posedge clk)
        out[1] == ((state == S4) || (state == S5) || (state == S6) || (state == S7))
    );

    // In S0, next_state depends only on in[0].
    check_next_state_s0: assert property (
        @(posedge clk)
        (state == S0) |-> (next_state == (in[0] ? S1 : S0))
    );

    // In S1, next_state depends only on in[1].
    check_next_state_s1: assert property (
        @(posedge clk)
        (state == S1) |-> (next_state == (in[1] ? S3 : S2))
    );

    // In S2, next_state depends only on in[2].
    check_next_state_s2: assert property (
        @(posedge clk)
        (state == S2) |-> (next_state == (in[2] ? S3 : S1))
    );

    // In S3, next_state depends only on in[3].
    check_next_state_s3: assert property (
        @(posedge clk)
        (state == S3) |-> (next_state == (in[3] ? S4 : S0))
    );

    // In S4, next_state depends only on in[0].
    check_next_state_s4: assert property (
        @(posedge clk)
        (state == S4) |-> (next_state == (in[0] ? S5 : S4))
    );

    // In S5, next_state depends only on in[1].
    check_next_state_s5: assert property (
        @(posedge clk)
        (state == S5) |-> (next_state == (in[1] ? S7 : S6))
    );

    // In S6, next_state depends only on in[2].
    check_next_state_s6: assert property (
        @(posedge clk)
        (state == S6) |-> (next_state == (in[2] ? S7 : S5))
    );

    // In S7, next_state depends only on in[3].
    check_next_state_s7: assert property (
        @(posedge clk)
        (state == S7) |-> (next_state == (in[3] ? S0 : S4))
    );

    // The state register loads the previous cycle's next_state.
    check_state_register_update: assert property (
        @(posedge clk)
        1'b1 |=> (state == $past(next_state))
    );

endmodule