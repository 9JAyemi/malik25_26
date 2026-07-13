module sky130_fd_sc_hd__nor3_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Y implements ~(A | B | C) on any input/output edge.
    check_nor_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            Y == ~(A | B | C)
    );

    // When all inputs are LOW, Y must be HIGH.
    check_y_high_when_all_inputs_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (!A && !B && !C) |-> (Y == 1'b1)
    );

    // When any input is HIGH, Y must be LOW.
    check_y_low_when_any_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (A || B || C) |-> (Y == 1'b0)
    );

    // If Y is HIGH, then all inputs must be LOW.
    check_y_one_implies_all_inputs_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (Y == 1'b1) |-> (!A && !B && !C)
    );

    // If Y is LOW, at least one input must be HIGH.
    check_y_zero_implies_any_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (Y == 1'b0) |-> (A || B || C)
    );

    // With B=C=0, Y must equal ~A.
    check_invert_A_when_BC_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (!B && !C) |-> (Y == ~A)
    );

    // With A=C=0, Y must equal ~B.
    check_invert_B_when_AC_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (!A && !C) |-> (Y == ~B)
    );

    // With A=B=0, Y must equal ~C.
    check_invert_C_when_AB_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge Y or negedge Y)
            (!A && !B) |-> (Y == ~C)
    );

    // A rising HIGH forces Y LOW in the same cycle.
    check_rise_A_forces_Y_low: assert property (
        @(posedge A) (Y == 1'b0)
    );

    // B rising HIGH forces Y LOW in the same cycle.
    check_rise_B_forces_Y_low: assert property (
        @(posedge B) (Y == 1'b0)
    );

    // C rising HIGH forces Y LOW in the same cycle.
    check_rise_C_forces_Y_low: assert property (
        @(posedge C) (Y == 1'b0)
    );
endmodule