module top_module_sva (
    input logic [3:0] I,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] result
);

    // No explicit clock or reset exists in the RTL; sample combinational behavior on $global_clock.

    // I=0001 selects the base adder/subtractor result.
    check_result_i_0001: assert property (
        @($global_clock) (I == 4'b0001) |-> (result == (SUB ? (A - B) : (A + B)))
    );

    // I=0010 selects the base adder/subtractor result plus 1.
    check_result_i_0010: assert property (
        @($global_clock) (I == 4'b0010) |-> (result == ((SUB ? (A - B) : (A + B)) + 4'd1))
    );

    // I=0100 selects the base adder/subtractor result plus 2.
    check_result_i_0100: assert property (
        @($global_clock) (I == 4'b0100) |-> (result == ((SUB ? (A - B) : (A + B)) + 4'd2))
    );

    // I=1000 selects the base adder/subtractor result plus 3.
    check_result_i_1000: assert property (
        @($global_clock) (I == 4'b1000) |-> (result == ((SUB ? (A - B) : (A + B)) + 4'd3))
    );

    // All other I values use the encoder default and add no offset.
    check_result_i_default: assert property (
        @($global_clock)
        ((I != 4'b0001) && (I != 4'b0010) && (I != 4'b0100) && (I != 4'b1000))
        |-> (result == (SUB ? (A - B) : (A + B)))
    );

endmodule