module FSM_sva #(
    parameter int n = 4,
    parameter int m = 2,
    parameter int s = 8
) (
    input  logic [n-1:0] in,
    input  logic [m-1:0] out,
    input  logic         clk,
    input  logic [2:0]   state,
    input  logic [2:0]   next_state
);

    localparam logic [2:0] S0 = 3'b000;
    localparam logic [2:0] S1 = 3'b001;
    localparam logic [2:0] S2 = 3'b010;
    localparam logic [2:0] S3 = 3'b011;
    localparam logic [2:0] S4 = 3'b100;
    localparam logic [2:0] S5 = 3'b101;
    localparam logic [2:0] S6 = 3'b110;
    localparam logic [2:0] S7 = 3'b111;

    localparam logic [m-1:0] O0 = 2'b00;
    localparam logic [m-1:0] O1 = 2'b01;
    localparam logic [m-1:0] O2 = 2'b10;
    localparam logic [m-1:0] O3 = 2'b11;

    // State register loads the previous next_state value.
    check_state_updates_from_next_state: assert property (
        @(posedge clk) !$isunknown($past(next_state)) |-> (state == $past(next_state))
    );

    // Output remains stable when state remains stable.
    check_out_stable_when_state_stable: assert property (
        @(posedge clk)
        !$isunknown($past(state)) && !$isunknown($past(out)) && (state == $past(state))
        |-> (out == $past(out))
    );

    // S0 drives O0.
    check_out_decode_s0: assert property (
        @(posedge clk) (state == S0) |-> (out == O0)
    );

    // S1 drives O1.
    check_out_decode_s1: assert property (
        @(posedge clk) (state == S1) |-> (out == O1)
    );

    // S2 drives O2.
    check_out_decode_s2: assert property (
        @(posedge clk) (state == S2) |-> (out == O2)
    );

    // S3 drives O3.
    check_out_decode_s3: assert property (
        @(posedge clk) (state == S3) |-> (out == O3)
    );

    // S4 drives O0.
    check_out_decode_s4: assert property (
        @(posedge clk) (state == S4) |-> (out == O0)
    );

    // S5 drives O1.
    check_out_decode_s5: assert property (
        @(posedge clk) (state == S5) |-> (out == O1)
    );

    // S6 drives O2.
    check_out_decode_s6: assert property (
        @(posedge clk) (state == S6) |-> (out == O2)
    );

    // S7 drives O3.
    check_out_decode_s7: assert property (
        @(posedge clk) (state == S7) |-> (out == O3)
    );

endmodule