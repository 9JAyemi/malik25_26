module Contador_AD_Minutos_sva #(
    parameter int N = 6,
    parameter [N-1:0] X = 59
) (
    input logic rst,
    input logic [7:0] estado,
    input logic [1:0] en,
    input logic [7:0] Cambio,
    input logic got_data,
    input logic clk,
    input logic [N-1:0] Cuenta
);

    // Reset clears the counter.
    check_reset_clears_cuenta: assert property (
        @(posedge clk) rst |=> (Cuenta == '0)
    );

    // Counter holds when enable is not 1.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (en != 2'd1) |=> (Cuenta == $past(Cuenta))
    );

    // Counter holds when estado is not 6C or 75.
    check_hold_when_estado_not_allowed: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && !((estado == 8'h6C) || (estado == 8'h75)))
        |=> (Cuenta == $past(Cuenta))
    );

    // Counter holds in active states when got_data is low.
    check_hold_without_got_data: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) && !got_data)
        |=> (Cuenta == $past(Cuenta))
    );

    // Counter holds when Cambio is not 73 or 72.
    check_hold_on_unrecognized_cambio: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) && got_data &&
         !((Cambio == 8'h73) || (Cambio == 8'h72)))
        |=> (Cuenta == $past(Cuenta))
    );

    // Increment wraps from X to zero.
    check_increment_wraps_at_x: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) &&
         (Cambio == 8'h73) && got_data && (Cuenta == X))
        |=> (Cuenta == '0)
    );

    // Increment advances by one below X.
    check_increment_advances_by_one: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) &&
         (Cambio == 8'h73) && got_data && (Cuenta != X))
        |=> (Cuenta == ($past(Cuenta) + {{(N-1){1'b0}}, 1'b1}))
    );

    // Decrement wraps from zero to X.
    check_decrement_wraps_at_zero: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) &&
         (Cambio == 8'h72) && got_data && (Cuenta == '0))
        |=> (Cuenta == X)
    );

    // Decrement decreases by one above zero.
    check_decrement_decreases_by_one: assert property (
        @(posedge clk) disable iff (rst)
        ((en == 2'd1) && ((estado == 8'h6C) || (estado == 8'h75)) &&
         (Cambio == 8'h72) && got_data && (Cuenta != '0))
        |=> (Cuenta == ($past(Cuenta) - {{(N-1){1'b0}}, 1'b1}))
    );

endmodule