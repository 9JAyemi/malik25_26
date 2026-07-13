module sky130_fd_sc_ls__xnor2_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic Y
);
    // Output equals bitwise XNOR of inputs at all times.
    check_function_equivalence: assert property (
        @(posedge CLK) (Y === ~(A ^ B))
    );

    // When inputs are known and equal, output must be 1.
    check_equal_known_implies_one: assert property (
        @(posedge CLK) (! $isunknown({A,B}) && (A == B)) |-> (Y == 1'b1)
    );

    // When inputs are known and not equal, output must be 0.
    check_unequal_known_implies_zero: assert property (
        @(posedge CLK) (! $isunknown({A,B}) && (A != B)) |-> (Y == 1'b0)
    );

    // When both inputs are known, output must be known (no X/Z).
    check_known_inputs_imply_known_output: assert property (
        @(posedge CLK) (! $isunknown({A,B})) |-> (! $isunknown(Y))
    );

    // If exactly one input changed since last cycle, output must change.
    check_single_input_toggle_flips_output: assert property (
        @(posedge CLK) (($changed(A) ^ $changed(B))) |-> $changed(Y)
    );

    // If both inputs changed since last cycle, output must not change.
    check_both_inputs_toggle_keep_output: assert property (
        @(posedge CLK) ($changed(A) && $changed(B)) |-> (!$changed(Y))
    );

    // If neither input changed since last cycle, output must not change.
    check_no_input_change_keeps_output: assert property (
        @(posedge CLK) ((!$changed(A)) && (!$changed(B))) |-> (!$changed(Y))
    );
endmodule