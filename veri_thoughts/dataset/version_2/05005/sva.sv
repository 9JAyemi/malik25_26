module MUX41X1_sva (
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic IN4,
    input logic S0,
    input logic S1,
    input logic Q
);

    // Q matches the complete mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        Q == ((S0 & ((S1 & IN1) | (~S1 & IN2))) |
              (~S0 & ((S1 & IN3) | (~S1 & IN4))))
    );

    // When S0 selects the upper branch, Q follows the IN1/IN2 choice.
    check_upper_branch_select: assert property (
        @($global_clock)
        (S0 == 1'b1) |-> (Q == ((S1 & IN1) | (~S1 & IN2)))
    );

    // When S0 selects the lower branch, Q follows the IN3/IN4 choice.
    check_lower_branch_select: assert property (
        @($global_clock)
        (S0 == 1'b0) |-> (Q == ((S1 & IN3) | (~S1 & IN4)))
    );

    // S0=1 and S1=1 select IN1.
    check_select_in1: assert property (
        @($global_clock)
        ((S0 == 1'b1) && (S1 == 1'b1)) |-> (Q == IN1)
    );

    // S0=1 and S1=0 select IN2.
    check_select_in2: assert property (
        @($global_clock)
        ((S0 == 1'b1) && (S1 == 1'b0)) |-> (Q == IN2)
    );

    // S0=0 and S1=1 select IN3.
    check_select_in3: assert property (
        @($global_clock)
        ((S0 == 1'b0) && (S1 == 1'b1)) |-> (Q == IN3)
    );

    // S0=0 and S1=0 select IN4.
    check_select_in4: assert property (
        @($global_clock)
        ((S0 == 1'b0) && (S1 == 1'b0)) |-> (Q == IN4)
    );

endmodule