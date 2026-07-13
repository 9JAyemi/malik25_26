module my_module_sva (
    // DUT ports as inputs
    input logic VPWR,
    input logic VGND,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    // Internal signals from DUT
    input logic and0_out,
    input logic and1_out,
    input logic or0_out_X,
    input logic buf0_out
);
    // No clock/reset in RTL; purely combinational: X = (A3 & A1 & A2) | (B1 & B2)

    // AND gate and0 implements A3 & A1 & A2.
    check_and0_gate_function: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            and0_out === (A3 & A1 & A2)
    );

    // AND gate and1 implements B1 & B2.
    check_and1_gate_function: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            and1_out === (B1 & B2)
    );

    // OR gate or0 implements and1_out | and0_out.
    check_or0_gate_function: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            or0_out_X === (and1_out | and0_out)
    );

    // BUF gate buf0 passes or0_out_X to buf0_out.
    check_buf0_identity: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            buf0_out === or0_out_X
    );

    // Final assign connects buf0_out to X.
    check_output_assign_identity: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            X === buf0_out
    );

    // End-to-end function: X == (A3 & A1 & A2) | (B1 & B2).
    check_end_to_end_equation: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            X === ((A3 & A1 & A2) | (B1 & B2))
    );

    // If either AND path is 1, X must be 1 (same cycle).
    check_output_one_if_any_path_one: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            ((and0_out === 1'b1) || (and1_out === 1'b1)) |-> (X === 1'b1)
    );

    // If both AND paths are 0, X must be 0 (same cycle).
    check_output_zero_if_both_paths_zero: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            ((and0_out === 1'b0) && (and1_out === 1'b0)) |-> (X === 1'b0)
    );

    // X=1 implies at least one AND path is 1.
    check_output_high_implies_any_path_high: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            (X === 1'b1) |-> ((and0_out === 1'b1) || (and1_out === 1'b1))
    );

    // X=0 implies both AND paths are 0.
    check_output_low_implies_both_paths_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge X or posedge and0_out or posedge and1_out or posedge or0_out_X or posedge buf0_out)
            (X === 1'b0) |-> ((and0_out === 1'b0) && (and1_out === 1'b0))
    );

endmodule