module OA22X1_sva (
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic IN4,
    input logic Q,
    input logic VDD,
    input logic VSS
);

    // Q matches the implemented conditional combinational function.
    check_output_function: assert property (
        @($global_clock)
        Q === (
            (IN1 & ~IN2) ? IN3 :
            ((~IN1 & IN2) ? IN4 :
            ((IN1 & IN2) ? (IN3 & IN4) :
                           (IN3 | IN4)))
        )
    );

    // IN1=1 and IN2=0 selects IN3.
    check_select_in3: assert property (
        @($global_clock)
        ((IN1 === 1'b1) && (IN2 === 1'b0)) |-> (Q === IN3)
    );

    // IN1=0 and IN2=1 selects IN4.
    check_select_in4: assert property (
        @($global_clock)
        ((IN1 === 1'b0) && (IN2 === 1'b1)) |-> (Q === IN4)
    );

    // IN1=1 and IN2=1 selects IN3 & IN4.
    check_and_mode: assert property (
        @($global_clock)
        ((IN1 === 1'b1) && (IN2 === 1'b1)) |-> (Q === (IN3 & IN4))
    );

    // IN1=0 and IN2=0 selects IN3 | IN4.
    check_or_mode: assert property (
        @($global_clock)
        ((IN1 === 1'b0) && (IN2 === 1'b0)) |-> (Q === (IN3 | IN4))
    );

    // Both data inputs low force Q low.
    check_both_data_low_force_zero: assert property (
        @($global_clock)
        ((IN3 === 1'b0) && (IN4 === 1'b0)) |-> (Q === 1'b0)
    );

    // Both data inputs high force Q high.
    check_both_data_high_force_one: assert property (
        @($global_clock)
        ((IN3 === 1'b1) && (IN4 === 1'b1)) |-> (Q === 1'b1)
    );

    // Stable functional inputs keep Q stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock)
        ($stable(IN1) && $stable(IN2) && $stable(IN3) && $stable(IN4)) |-> $stable(Q)
    );

    // Supply pin changes do not affect Q when functional inputs are unchanged.
    check_supply_independence: assert property (
        @($global_clock)
        ($stable(IN1) && $stable(IN2) && $stable(IN3) && $stable(IN4) &&
         (!$stable(VDD) || !$stable(VSS))) |-> $stable(Q)
    );

endmodule