module Arithmetic_Logic_Operations_sva(
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [2:0] op,
    input logic sel,
    input logic [7:0] out
);

    // When sel is low, out bypasses directly from a.
    check_bypass_when_sel_low: assert property (
        @($global_clock) (!sel) |-> (out == a)
    );

    // When selected and op is 000, out is a + b.
    check_add_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b000)) |-> (out == (a + b))
    );

    // When selected and op is 001, out is a - b.
    check_sub_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b001)) |-> (out == (a - b))
    );

    // When selected and op is 010, out is a & b.
    check_and_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b010)) |-> (out == (a & b))
    );

    // When selected and op is 011, out is a | b.
    check_or_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b011)) |-> (out == (a | b))
    );

    // When selected and op is 100, out is a ^ b.
    check_xor_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b100)) |-> (out == (a ^ b))
    );

    // When selected and op is 101, out is bitwise not of a.
    check_not_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b101)) |-> (out == (~a))
    );

    // When selected and op is 110, out is a shifted left by b.
    check_shift_left_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b110)) |-> (out == (a << b))
    );

    // When selected and op is 111, out is a shifted right by b.
    check_shift_right_when_selected: assert property (
        @($global_clock) (sel && (op == 3'b111)) |-> (out == (a >> b))
    );

endmodule