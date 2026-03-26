module Contador_AD_sva #(
    parameter int N = 6,
    parameter int X = 59
) (
    input logic rst,
    input logic [1:0] en,
    input logic [7:0] Cambio,
    input logic got_data,
    input logic clk,
    input logic [N-1:0] Cuenta
);

    localparam logic [N-1:0] X_VAL = X;
    localparam logic [N-1:0] ONE   = {{(N-1){1'b0}}, 1'b1};

    // en==0 with rst high clears Cuenta.
    check_reset_when_en_zero: assert property (
        @(posedge clk) (en == 2'd0 && rst) |=> (Cuenta == '0)
    );

    // en==0 with rst low holds Cuenta.
    check_hold_when_en_zero_without_reset: assert property (
        @(posedge clk) (en == 2'd0 && !rst) |=> $stable(Cuenta)
    );

    // Valid up command at X wraps Cuenta to zero.
    check_increment_wrap_at_x: assert property (
        @(posedge clk) (en == 2'd1 && Cambio == 8'h75 && got_data && Cuenta == X_VAL) |=> (Cuenta == '0)
    );

    // Valid up command below X increments Cuenta by one.
    check_increment_step_below_x: assert property (
        @(posedge clk) (en == 2'd1 && Cambio == 8'h75 && got_data && Cuenta != X_VAL) |=> (Cuenta == ($past(Cuenta) + ONE))
    );

    // Valid down command at zero wraps Cuenta to X.
    check_decrement_wrap_at_zero: assert property (
        @(posedge clk) (en == 2'd2 && Cambio == 8'h72 && got_data && Cuenta == '0) |=> (Cuenta == X_VAL)
    );

    // Valid down command above zero decrements Cuenta by one.
    check_decrement_step_above_zero: assert property (
        @(posedge clk) (en == 2'd2 && Cambio == 8'h72 && got_data && Cuenta != '0) |=> (Cuenta == ($past(Cuenta) - ONE))
    );

    // en==1 with any non-matching command holds Cuenta.
    check_hold_on_invalid_up_command: assert property (
        @(posedge clk) (en == 2'd1 && !(Cambio == 8'h75 && got_data)) |=> $stable(Cuenta)
    );

    // en==2 with any non-matching command holds Cuenta.
    check_hold_on_invalid_down_command: assert property (
        @(posedge clk) (en == 2'd2 && !(Cambio == 8'h72 && got_data)) |=> $stable(Cuenta)
    );

    // en==3 always holds Cuenta.
    check_hold_when_en_three: assert property (
        @(posedge clk) (en == 2'd3) |=> $stable(Cuenta)
    );

endmodule