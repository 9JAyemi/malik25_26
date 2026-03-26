module mux4to1_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic [1:0] s,
    input logic y
);

    // No RTL clock or reset; sample combinational behavior on $global_clock.

    // When select is 00, output follows a.
    check_select_a: assert property (
        @($global_clock) (s == 2'b00) |-> (y == a)
    );

    // When select is 01, output follows b.
    check_select_b: assert property (
        @($global_clock) (s == 2'b01) |-> (y == b)
    );

    // When select is 10, output follows c.
    check_select_c: assert property (
        @($global_clock) (s == 2'b10) |-> (y == c)
    );

    // When select is 11, output follows d.
    check_select_d: assert property (
        @($global_clock) (s == 2'b11) |-> (y == d)
    );

endmodule