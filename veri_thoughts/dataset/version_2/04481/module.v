
module dff_with_async_set_reset(input D, SET, RESET, CLK, output Q);

    reg Q_reg = 0;

    always @(posedge CLK) // , posedge SET, negedge RESET)
    begin
        if (SET)
            Q_reg <= 1'b1;
        else if(RESET)
            Q_reg <= 1'b0;
        else
            Q_reg <= D;
    end

    assign Q = Q_reg;

endmodule