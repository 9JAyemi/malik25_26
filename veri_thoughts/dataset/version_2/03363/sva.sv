module logic_circuit_sva(
    input logic a,
    input logic b,
    input logic c,
    input logic x,
    input logic y,
    input logic z
);

    // x directly mirrors a.
    check_x_matches_a: assert property (
        @($global_clock) (x == a)
    );

    // y matches the a==0 and b==1 decode.
    check_y_decode: assert property (
        @($global_clock) (y == ((a == 1'b0) && (b == 1'b1)))
    );

    // z matches the a==0, b==0, c==1 decode.
    check_z_decode: assert property (
        @($global_clock) (z == ((a == 1'b0) && (b == 1'b0) && (c == 1'b1)))
    );

    // When a is high, only x can be high.
    check_a_high_forces_x_only: assert property (
        @($global_clock) (a == 1'b1) |-> ((x == 1'b1) && (y == 1'b0) && (z == 1'b0))
    );

    // y high implies the y decode state and excludes the other outputs.
    check_y_high_state: assert property (
        @($global_clock) (y == 1'b1) |-> ((a == 1'b0) && (b == 1'b1) && (x == 1'b0) && (z == 1'b0))
    );

    // z high implies the z decode state and excludes the other outputs.
    check_z_high_state: assert property (
        @($global_clock) (z == 1'b1) |-> ((a == 1'b0) && (b == 1'b0) && (c == 1'b1) && (x == 1'b0) && (y == 1'b0))
    );

    // y and z are mutually exclusive decodes.
    check_y_z_mutex: assert property (
        @($global_clock) !((y == 1'b1) && (z == 1'b1))
    );

endmodule