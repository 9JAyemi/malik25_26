
module and_gate (
    Y ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    reg Y_reg;

    always @ ( A1 or  A2 or  A3 or  A4 or  B1) begin
        if (A1 && A2 && A3 && A4 && B1) begin
            Y_reg <= 1'b1;
        end
        else begin
            Y_reg <= 1'b0;
        end
    end

    assign Y = Y_reg;

endmodule