module addsub8_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic add,
    input logic sub,
    input logic [7:0] Z
);

    // Z always matches the RTL's selected arithmetic function.
    check_selected_function: assert property (
        @($global_clock) Z == (add ? (A + B) : (sub ? (A - B) : 8'b0))
    );

    // When add is asserted, Z is the sum of A and B.
    check_add_result: assert property (
        @($global_clock) add |-> (Z == (A + B))
    );

    // When only sub is asserted, Z is the difference A minus B.
    check_sub_result: assert property (
        @($global_clock) (!add && sub) |-> (Z == (A - B))
    );

    // When neither operation is selected, Z is zero.
    check_zero_when_no_op: assert property (
        @($global_clock) (!add && !sub) |-> (Z == 8'b0)
    );

    // When both controls are high, add has priority over sub.
    check_add_priority: assert property (
        @($global_clock) (add && sub) |-> (Z == (A + B))
    );

endmodule