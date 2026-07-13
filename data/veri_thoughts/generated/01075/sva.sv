module comparator_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic Z
);
    ///// Functional correctness /////
    // When A equals B, Z must be HIGH.
    check_z_high_when_equal: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (Z == 1'b1)
    );
    // When A is greater than B, Z must be HIGH.
    check_z_high_when_greater: assert property (
        @(posedge CLK) disable iff (1'b0) (A > B) |-> (Z == 1'b1)
    );
    // When A is less than B, Z must be LOW.
    check_z_low_when_less: assert property (
        @(posedge CLK) disable iff (1'b0) (A < B) |-> (Z == 1'b0)
    );

    ///// Combinational consistency /////
    // If A and B are stable, Z must remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(A) && $stable(B)) |-> $stable(Z)
    );
    // Any change on Z must be caused by a change on A or B.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) disable iff (1'b0) $changed(Z) |-> ($changed(A) || $changed(B))
    );
endmodule