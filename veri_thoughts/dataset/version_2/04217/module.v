
module my_module (
    input  D,
    output Q,
    input  DE,
    input  SCD,
    input  SCE,
    input  CLK
);

    reg Q_reg; // register to hold previous value of Q

    always @(posedge CLK) begin
        if (SCD == 1'b0 && SCE == 1'b1) begin // if in scan chain, hold previous value of Q
            Q_reg <= Q_reg;
        end else begin
            if (DE == 1'b1) begin // if control signal is high, output data signal
                Q_reg <= D;
            end
        end
    end

    assign Q = Q_reg;

endmodule