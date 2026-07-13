module OneHotStateMachine_sva #(
    parameter n = 4
) (
    input logic clk,
    input logic [n-1:0] out,
    input logic [n-1:0] state
);

    localparam logic [n-1:0] OUT_STATE0 = 4'b0001;
    localparam logic [n-1:0] OUT_STATE1 = 4'b0010;
    localparam logic [n-1:0] OUT_STATE2 = 4'b0100;
    localparam logic [n-1:0] OUT_STATE3 = 4'b1000;

    // State 0 advances to state 1.
    check_state_0_to_1: assert property (
        @(posedge clk) (state == 0) |=> (state == 1)
    );

    // State 1 advances to state 2.
    check_state_1_to_2: assert property (
        @(posedge clk) (state == 1) |=> (state == 2)
    );

    // State 2 advances to state 3.
    check_state_2_to_3: assert property (
        @(posedge clk) (state == 2) |=> (state == 3)
    );

    // State 3 wraps back to state 0.
    check_state_3_to_0: assert property (
        @(posedge clk) (state == 3) |=> (state == 0)
    );

    // State 0 drives the first one-hot output.
    check_out_for_state_0: assert property (
        @(posedge clk) (state == 0) |-> (out == OUT_STATE0)
    );

    // State 1 drives the second one-hot output.
    check_out_for_state_1: assert property (
        @(posedge clk) (state == 1) |-> (out == OUT_STATE1)
    );

    // State 2 drives the third one-hot output.
    check_out_for_state_2: assert property (
        @(posedge clk) (state == 2) |-> (out == OUT_STATE2)
    );

    // State 3 drives the fourth one-hot output.
    check_out_for_state_3: assert property (
        @(posedge clk) (state == 3) |-> (out == OUT_STATE3)
    );

    // Known invalid states hold their value.
    check_invalid_state_holds: assert property (
        @(posedge clk)
        !((state == 0) || (state == 1) || (state == 2) || (state == 3))
        |=> $stable(state)
    );

    // Known invalid states leave the output unchanged.
    check_invalid_state_keeps_out_stable: assert property (
        @(posedge clk)
        !((state == 0) || (state == 1) || (state == 2) || (state == 3))
        |=> $stable(out)
    );

endmodule