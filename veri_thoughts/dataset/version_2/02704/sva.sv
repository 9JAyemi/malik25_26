module sky130_fd_sc_ms__nor3b_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);
    // Y equals C_N & ~(A | B) on any input edge.
    check_function_on_any_input_edge: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
            Y == (C_N & ~(A | B))
    );

    // Y can only be 1 when A=0, B=0, C_N=1 (checked on any input edge).
    check_y_high_implies_inputs: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
            (Y == 1'b1) |-> ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1))
    );

    // If A=0, B=0, C_N=1 at a sampling edge, Y must be 1.
    check_inputs_for_y_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
            ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1)) |-> (Y == 1'b1)
    );

    // If either A or B is 1 at a sampling edge, Y must be 0.
    check_a_or_b_high_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
            ((A == 1'b1) || (B == 1'b1)) |-> (Y == 1'b0)
    );

    // If C_N is 0 at a sampling edge, Y must be 0.
    check_c_n_low_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
            (C_N == 1'b0) |-> (Y == 1'b0)
    );

    // When C_N falls, Y must be 0 immediately.
    check_y_low_on_c_n_fall: assert property (
        @(negedge C_N) (Y == 1'b0)
    );

    // When A or B rises, Y must be 0 immediately.
    check_y_low_on_a_or_b_rise: assert property (
        @(posedge A or posedge B) (Y == 1'b0)
    );

    // When Y rises, inputs must be A=0, B=0, C_N=1.
    check_y_rise_condition: assert property (
        @(posedge Y) (A == 1'b0) && (B == 1'b0) && (C_N == 1'b1)
    );

    // Y can only change when at least one input changes in the same timestep.
    check_y_changes_only_with_input_change: assert property (
        @(posedge Y or negedge Y) $changed(A) || $changed(B) || $changed(C_N)
    );
endmodule