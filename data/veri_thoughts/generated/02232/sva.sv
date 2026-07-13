module MULTIPLEXER_4_TO_1_sva #(
    parameter BUS_WIDTH = 32
) (
    // External sampling clock for assertions (DUT has no clock/reset)
    input  logic                      CLK,
    // DUT ports
    input  logic [BUS_WIDTH-1:0]      IN1,
    input  logic [BUS_WIDTH-1:0]      IN2,
    input  logic [BUS_WIDTH-1:0]      IN3,
    input  logic [BUS_WIDTH-1:0]      IN4,
    input  logic [1:0]                SELECT,
    input  logic [BUS_WIDTH-1:0]      OUT
);
    // SELECT==00 routes IN1 to OUT in the same cycle.
    check_sel00_routes_IN1: assert property (
        @(posedge CLK) (SELECT == 2'b00) |-> (OUT == IN1)
    );

    // SELECT==01 routes IN2 to OUT in the same cycle.
    check_sel01_routes_IN2: assert property (
        @(posedge CLK) (SELECT == 2'b01) |-> (OUT == IN2)
    );

    // SELECT==10 routes IN3 to OUT in the same cycle.
    check_sel10_routes_IN3: assert property (
        @(posedge CLK) (SELECT == 2'b10) |-> (OUT == IN3)
    );

    // SELECT==11 routes IN4 to OUT in the same cycle.
    check_sel11_routes_IN4: assert property (
        @(posedge CLK) (SELECT == 2'b11) |-> (OUT == IN4)
    );

    // When SELECT==00 and IN1 changes, OUT matches IN1 that same cycle.
    check_propagation_sel00: assert property (
        @(posedge CLK) (SELECT == 2'b00 && $changed(IN1)) |-> (OUT == IN1)
    );

    // When SELECT==01 and IN2 changes, OUT matches IN2 that same cycle.
    check_propagation_sel01: assert property (
        @(posedge CLK) (SELECT == 2'b01 && $changed(IN2)) |-> (OUT == IN2)
    );

    // When SELECT==10 and IN3 changes, OUT matches IN3 that same cycle.
    check_propagation_sel10: assert property (
        @(posedge CLK) (SELECT == 2'b10 && $changed(IN3)) |-> (OUT == IN3)
    );

    // When SELECT==11 and IN4 changes, OUT matches IN4 that same cycle.
    check_propagation_sel11: assert property (
        @(posedge CLK) (SELECT == 2'b11 && $changed(IN4)) |-> (OUT == IN4)
    );

    // With SELECT==00 and IN1/SELECT stable, changes on other inputs do not affect OUT.
    check_isolation_sel00: assert property (
        @(posedge CLK) (SELECT == 2'b00 && $stable(SELECT) && $stable(IN1) && ($changed(IN2) || $changed(IN3) || $changed(IN4))) |-> $stable(OUT)
    );

    // With SELECT==01 and IN2/SELECT stable, changes on other inputs do not affect OUT.
    check_isolation_sel01: assert property (
        @(posedge CLK) (SELECT == 2'b01 && $stable(SELECT) && $stable(IN2) && ($changed(IN1) || $changed(IN3) || $changed(IN4))) |-> $stable(OUT)
    );

    // With SELECT==10 and IN3/SELECT stable, changes on other inputs do not affect OUT.
    check_isolation_sel10: assert property (
        @(posedge CLK) (SELECT == 2'b10 && $stable(SELECT) && $stable(IN3) && ($changed(IN1) || $changed(IN2) || $changed(IN4))) |-> $stable(OUT)
    );

    // With SELECT==11 and IN4/SELECT stable, changes on other inputs do not affect OUT.
    check_isolation_sel11: assert property (
        @(posedge CLK) (SELECT == 2'b11 && $stable(SELECT) && $stable(IN4) && ($changed(IN1) || $changed(IN2) || $changed(IN3))) |-> $stable(OUT)
    );
endmodule