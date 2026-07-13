module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       select,
    input logic [7:0] out_xor,
    input logic [7:0] out_and,
    input logic [7:0] out_not
);

    // No explicit clock or reset exists in the RTL; sample on the formal global clock.

    // out_xor must implement the select-controlled XOR/AND mux.
    check_out_xor_function: assert property (
        @($global_clock) out_xor == (select ? (a ^ b) : (a & b))
    );

    // out_and must implement the complementary select-controlled AND/XOR mux.
    check_out_and_function: assert property (
        @($global_clock) out_and == (select ? (a & b) : (a ^ b))
    );

    // out_not must equal the bitwise inversion of b.
    check_out_not_function: assert property (
        @($global_clock) out_not == ~b
    );

    // When select is high, out_xor is XOR and out_and is AND.
    check_select_high_routing: assert property (
        @($global_clock) select |-> ((out_xor == (a ^ b)) && (out_and == (a & b)))
    );

    // When select is low, out_xor is AND and out_and is XOR.
    check_select_low_routing: assert property (
        @($global_clock) !select |-> ((out_xor == (a & b)) && (out_and == (a ^ b)))
    );

endmodule