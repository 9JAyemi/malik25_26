module logic_func_4x2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic Y
);

    // X matches the implemented combinational equation.
    check_x_function: assert property (
        @($global_clock) X == ((A & B) | (C & D))
    );

    // Y matches the implemented combinational equation.
    check_y_function: assert property (
        @($global_clock) Y == ((A & C) | (B & D))
    );

endmodule