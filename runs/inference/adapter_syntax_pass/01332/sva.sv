module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       SUB,
    input logic [3:0] OUT
);

    // OUT must match the selected add or subtract operation.
    check_selected_operation: assert property (
        @($global_clock) OUT == (SUB ? (B - A) : (A + B))
    );

    // In add mode, OUT must equal A plus B.
    check_add_mode: assert property (
        @($global_clock) !SUB |-> (OUT == (A + B))
    );

    // In subtract mode, OUT must equal B minus A.
    check_sub_mode: assert property (
        @($global_clock) SUB |-> (OUT == (B - A))
    );

    // With B equal to zero, OUT must pass A through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> (OUT == A)
    );

    // With A equal to zero, OUT must pass B through.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> (OUT == B)
    );

endmodule