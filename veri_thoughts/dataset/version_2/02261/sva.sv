module bitwise_operations_sva (
    input logic [0:7] in,
    input logic B1,
    input logic B2,
    input logic B3,
    input logic B4,
    input logic B5,
    input logic B6,
    input logic B7,
    input logic B8,
    input logic B9,
    input logic B10
);
    // No clock/reset in RTL; pure combinational; sample on global formal clock.

    // B1 equals in[0] & in[1].
    check_B1_and: assert property (
        @(posedge $global_clock) B1 === (in[0] & in[1])
    );

    // B2 equals in[0] | in[1].
    check_B2_or: assert property (
        @(posedge $global_clock) B2 === (in[0] | in[1])
    );

    // B3 equals ~(in[0] & in[1]) (NAND).
    check_B3_nand: assert property (
        @(posedge $global_clock) B3 === ~(in[0] & in[1])
    );

    // B4 equals ~(in[0] | in[1]) (NOR).
    check_B4_nor: assert property (
        @(posedge $global_clock) B4 === ~(in[0] | in[1])
    );

    // B5 equals in[0] ^ in[1] (XOR).
    check_B5_xor: assert property (
        @(posedge $global_clock) B5 === (in[0] ^ in[1])
    );

    // B6 equals ~(in[0] ^ in[1]) (XNOR).
    check_B6_xnor: assert property (
        @(posedge $global_clock) B6 === ~(in[0] ^ in[1])
    );

    // B7 equals ~in[0].
    check_B7_not_in0: assert property (
        @(posedge $global_clock) B7 === ~in[0]
    );

    // B8 equals in[0].
    check_B8_buf_in0: assert property (
        @(posedge $global_clock) B8 === in[0]
    );

    // B9 equals (in[0]&in[1]) && (in[2]&in[3]).
    check_B9_logical_and_pairs: assert property (
        @(posedge $global_clock) B9 === ((in[0] & in[1]) && (in[2] & in[3]))
    );

    // B10 equals (in[0]&in[1]) || (in[2]&in[3]).
    check_B10_logical_or_pairs: assert property (
        @(posedge $global_clock) B10 === ((in[0] & in[1]) || (in[2] & in[3]))
    );

endmodule