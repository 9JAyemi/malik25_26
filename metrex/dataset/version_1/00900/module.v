module Contador_AD_Dia(
    input rst,
    input [7:0]estado,
    input [1:0] en,
    input [7:0] Cambio,
    input got_data,
    input clk,
    output reg [(N-1):0] Cuenta
);

    parameter N = 7;
    parameter X = 99;

    always @(posedge clk) begin
        if (rst) begin
            Cuenta <= 1;
        end else if (en == 2'd2 && estado == 8'h7D) begin
            if (Cambio == 8'h73 && got_data) begin
                if (Cuenta == X) begin
                    Cuenta <= 1;
                end else begin
                    Cuenta <= Cuenta + 1'd1;
                end
            end else if (Cambio == 8'h72 && got_data) begin
                if (Cuenta == 1) begin
                    Cuenta <= X;
                end else begin
                    Cuenta <= Cuenta - 1'd1;
                end
            end else begin
                Cuenta <= Cuenta;
            end
        end else begin
            Cuenta <= Cuenta;
        end
    end

endmodule