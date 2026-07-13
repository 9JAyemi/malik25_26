module sky130_fd_sc_hs__nor4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic Y,
    input logic VPWR,
    input logic VGND
);

    // Y implements ~(A|B|C|D_N) whenever any input or Y changes.
    check_function_equivalence_on_change: assert property (
        @(posedge A or negedge A or
          posedge B or negedge B or
          posedge C or negedge C or
          posedge D_N or negedge D_N or
          posedge Y or negedge Y)
        (Y == ~(A | B | C | D_N))
    );

    // A rising forces Y LOW.
    check_A_rise_forces_Y_low: assert property (
        @(posedge A) (Y == 1'b0)
    );

    // B rising forces Y LOW.
    check_B_rise_forces_Y_low: assert property (
        @(posedge B) (Y == 1'b0)
    );

    // C rising forces Y LOW.
    check_C_rise_forces_Y_low: assert property (
        @(posedge C) (Y == 1'b0)
    );

    // D_N rising forces Y LOW.
    check_DN_rise_forces_Y_low: assert property (
        @(posedge D_N) (Y == 1'b0)
    );

    // Y can only rise when all inputs are LOW.
    check_Y_rise_requires_all_inputs_low: assert property (
        @(posedge Y) (A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b0)
    );

    // Y can only fall when any input is HIGH.
    check_Y_fall_requires_some_input_high: assert property (
        @(negedge Y) (A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D_N == 1'b1)
    );

    // If A is the last input going LOW (others LOW), Y must be HIGH.
    check_last_low_A_sets_Y_high: assert property (
        @(negedge A) ((B == 1'b0) && (C == 1'b0) && (D_N == 1'b0)) |-> (Y == 1'b1)
    );

    // If B is the last input going LOW (others LOW), Y must be HIGH.
    check_last_low_B_sets_Y_high: assert property (
        @(negedge B) ((A == 1'b0) && (C == 1'b0) && (D_N == 1'b0)) |-> (Y == 1'b1)
    );

    // If C is the last input going LOW (others LOW), Y must be HIGH.
    check_last_low_C_sets_Y_high: assert property (
        @(negedge C) ((A == 1'b0) && (B == 1'b0) && (D_N == 1'b0)) |-> (Y == 1'b1)
    );

    // If D_N is the last input going LOW (others LOW), Y must be HIGH.
    check_last_low_DN_sets_Y_high: assert property (
        @(negedge D_N) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (Y == 1'b1)
    );

endmodule