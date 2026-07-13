module my_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    ///// Combinational function checks /////
    // X equals (~(A2_N & A1_N)) & (B1 | B2).
    check_x_boolean_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ((~(A2_N & A1_N)) & (B1 | B2))
    );

    // If both A1_N and A2_N are 1, X must be 0.
    check_x_zero_when_A_both_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1_N && A2_N) |-> (X == 1'b0)
    );

    // If both B1 and B2 are 0, X must be 0.
    check_x_zero_when_B_both_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (!B1 && !B2) |-> (X == 1'b0)
    );

    // If (B1|B2)=1 and any A*_N is 0, X must be 1.
    check_x_one_when_B_or_and_any_A_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B1 || B2) && (!A1_N || !A2_N)) |-> (X == 1'b1)
    );

    // X high implies B1 or B2 is high.
    check_x_high_implies_B_or: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> (B1 || B2)
    );

    // X high implies not(A1_N & A2_N).
    check_x_high_implies_not_A_and: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> !(A1_N && A2_N)
    );

    // X high implies both conditions: (B1|B2)=1 and not(A1_N & A2_N).
    check_x_high_implies_required_conditions: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> ((B1 || B2) && !(A1_N && A2_N))
    );

    // Output can only change when at least one input changes.
    check_x_changes_only_with_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(X) |-> $changed({A1_N, A2_N, B1, B2})
    );
endmodule