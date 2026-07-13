module FSM_merge_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out,
    input logic [1:0] state,
    input logic [1:0] current_state,
    input logic [1:0] next_state
);

    localparam [1:0] STATE_A = 2'b00;
    localparam [1:0] STATE_B = 2'b01;
    localparam [1:0] STATE_C = 2'b10;
    localparam [1:0] STATE_D = 2'b11;

    localparam [1:0] MERGED_AB = 2'b00;
    localparam [1:0] MERGED_CD = 2'b01;

    // current_state loads the previously computed next_state on each clock.
    check_state_register_updates: assert property (
        @(posedge clk) 1'b1 |=> (current_state == $past(next_state))
    );

    // STATE_A with in[0] and in[1] high goes to STATE_B and drives out=01.
    check_state_a_true_branch: assert property (
        @(posedge clk) ((current_state == STATE_A) && in[0] && in[1]) |-> ((next_state == STATE_B) && (out == 2'b01))
    );

    // STATE_A otherwise goes to STATE_C and drives out=10.
    check_state_a_false_branch: assert property (
        @(posedge clk) ((current_state == STATE_A) && !(in[0] && in[1])) |-> ((next_state == STATE_C) && (out == 2'b10))
    );

    // STATE_B with in[2] high goes to STATE_C and drives out=10.
    check_state_b_true_branch: assert property (
        @(posedge clk) ((current_state == STATE_B) && in[2]) |-> ((next_state == STATE_C) && (out == 2'b10))
    );

    // STATE_B otherwise goes to STATE_D and drives out=11.
    check_state_b_false_branch: assert property (
        @(posedge clk) ((current_state == STATE_B) && !in[2]) |-> ((next_state == STATE_D) && (out == 2'b11))
    );

    // STATE_C with in[3] high goes to STATE_A and drives out=01.
    check_state_c_true_branch: assert property (
        @(posedge clk) ((current_state == STATE_C) && in[3]) |-> ((next_state == STATE_A) && (out == 2'b01))
    );

    // STATE_C otherwise goes to STATE_D and drives out=11.
    check_state_c_false_branch: assert property (
        @(posedge clk) ((current_state == STATE_C) && !in[3]) |-> ((next_state == STATE_D) && (out == 2'b11))
    );

    // STATE_D with all inputs high goes to STATE_A and drives out=00.
    check_state_d_true_branch: assert property (
        @(posedge clk) ((current_state == STATE_D) && in[0] && in[1] && in[2] && in[3]) |-> ((next_state == STATE_A) && (out == 2'b00))
    );

    // STATE_D otherwise goes to STATE_B and drives out=01.
    check_state_d_false_branch: assert property (
        @(posedge clk) ((current_state == STATE_D) && !(in[0] && in[1] && in[2] && in[3])) |-> ((next_state == STATE_B) && (out == 2'b01))
    );

    // STATE_A and STATE_B map to merged state 00.
    check_merged_state_ab: assert property (
        @(posedge clk) (((current_state == STATE_A) || (current_state == STATE_B)) |-> (state == MERGED_AB))
    );

    // STATE_C and STATE_D map to merged state 01.
    check_merged_state_cd: assert property (
        @(posedge clk) (((current_state == STATE_C) || (current_state == STATE_D)) |-> (state == MERGED_CD))
    );

endmodule