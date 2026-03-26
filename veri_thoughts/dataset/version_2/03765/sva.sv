module MUX_sva (
    input logic        clk,
    input logic [7:0]  Estado,
    input logic [5:0]  Cuenta_Segundos,
    input logic [5:0]  Cuenta_Minutos,
    input logic [4:0]  Cuenta_Horas,
    input logic [4:0]  Cuenta_Year,
    input logic [3:0]  Cuenta_Mes,
    input logic [6:0]  Cuenta_Dia,
    input logic [7:0]  Salida_1,
    input logic [7:0]  Salida_2,
    input logic [7:0]  Salida_3
);

    // Estado 6C selects seconds, minutes, and hours on the next cycle.
    check_estado_6c_selects_time: assert property (
        @(posedge clk)
        (Estado == 8'h6C) |=> (
            (Salida_1 == {2'b00, $past(Cuenta_Segundos)}) &&
            (Salida_2 == {2'b00, $past(Cuenta_Minutos)}) &&
            (Salida_3 == {3'b000, $past(Cuenta_Horas)})
        )
    );

    // Estado 75 selects seconds, minutes, and hours on the next cycle.
    check_estado_75_selects_time: assert property (
        @(posedge clk)
        (Estado == 8'h75) |=> (
            (Salida_1 == {2'b00, $past(Cuenta_Segundos)}) &&
            (Salida_2 == {2'b00, $past(Cuenta_Minutos)}) &&
            (Salida_3 == {3'b000, $past(Cuenta_Horas)})
        )
    );

    // All other Estado values select year, month, and day on the next cycle.
    check_other_estado_selects_date: assert property (
        @(posedge clk)
        (Estado != 8'h6C && Estado != 8'h75) |=> (
            (Salida_1 == {3'b000, $past(Cuenta_Year)}) &&
            (Salida_2 == {4'b0000, $past(Cuenta_Mes)}) &&
            (Salida_3 == {1'b0, $past(Cuenta_Dia)})
        )
    );

endmodule