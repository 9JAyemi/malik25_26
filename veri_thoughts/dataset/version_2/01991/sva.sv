module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       MODE,
    input logic [3:0] S
);
    // No clock/reset in DUT; pure combinational. Sample on any edge of inputs.
    default clocking cb @(
        posedge MODE or negedge MODE or
        posedge A[0] or negedge A[0] or
        posedge A[1] or negedge A[1] or
        posedge A[2] or negedge A[2] or
        posedge A[3] or negedge A[3] or
        posedge B[0] or negedge B[0] or
        posedge B[1] or negedge B[1] or
        posedge B[2] or negedge B[2] or
        posedge B[3] or negedge B[3]
    ); endclocking

    ///// Functional correctness /////
    // In add mode (MODE==0), S equals A + B (4-bit wraparound).
    check_add_mode: assert property (
        MODE == 1'b0 |-> (S == (A + B))
    );

    // In subtract mode (MODE==1), S equals A - B (4-bit wraparound).
    check_sub_mode: assert property (
        MODE == 1'b1 |-> (S == (A - B))
    );

    // Output equals the selected operation for all input combinations.
    check_function_selection: assert property (
        S == (MODE ? (A - B) : (A + B))
    );

    // If S changed between samples, at least one input changed as well.
    check_output_change_implies_input_change: assert property (
        $changed(S) |-> $changed({MODE, A, B})
    );
endmodule