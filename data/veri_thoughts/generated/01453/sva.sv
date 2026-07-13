module fsm_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic [2:0] currentState,
    input logic [2:0] nextState
);
    // State encodings (match RTL)
    localparam logic [2:0] s0 = 3'b000;
    localparam logic [2:0] s1 = 3'b001;
    localparam logic [2:0] s2 = 3'b010;
    localparam logic [2:0] s3 = 3'b011;
    localparam logic [2:0] s4 = 3'b100;
    localparam logic [2:0] s5 = 3'b101;

    // currentState captures previous-cycle nextState on each rising clock edge.
    check_state_register_updates_from_next: assert property (
        @(posedge clk) !$isunknown($past(nextState)) |-> (currentState == $past(nextState))
    );

    // From s0 with in==0, nextState is s1.
    check_s0_in0_go_s1: assert property (
        @(posedge clk) (currentState == s0 && in == 1'b0) |-> (nextState == s1)
    );

    // From s1 with in==0, nextState is s2.
    check_s1_in0_go_s2: assert property (
        @(posedge clk) (currentState == s1 && in == 1'b0) |-> (nextState == s2)
    );

    // From s2 with in==0, nextState is s3.
    check_s2_in0_go_s3: assert property (
        @(posedge clk) (currentState == s2 && in == 1'b0) |-> (nextState == s3)
    );

    // From s3 with in==0, nextState is s4.
    check_s3_in0_go_s4: assert property (
        @(posedge clk) (currentState == s3 && in == 1'b0) |-> (nextState == s4)
    );

    // From s4 with in==0, nextState is s5.
    check_s4_in0_go_s5: assert property (
        @(posedge clk) (currentState == s4 && in == 1'b0) |-> (nextState == s5)
    );

    // With in==1 and a defined state, nextState is s5.
    check_in1_forces_s5_from_any: assert property (
        @(posedge clk) (in == 1'b1 && (currentState inside {s0,s1,s2,s3,s4,s5})) |-> (nextState == s5)
    );

    // State s5 is absorbing regardless of input.
    check_s5_absorbing: assert property (
        @(posedge clk) (currentState == s5) |-> (nextState == s5)
    );

    // out reflects whether currentState is s5.
    check_out_matches_state: assert property (
        @(posedge clk) out == (currentState == s5)
    );

    // Once out is HIGH, it remains HIGH (since s5 is absorbing).
    check_out_sticky_when_high: assert property (
        @(posedge clk) out |-> ##1 out
    );

endmodule