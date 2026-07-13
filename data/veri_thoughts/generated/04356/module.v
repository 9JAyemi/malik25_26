
module even_parity_checker(
    input D0, D1, D2, D3, RST, ECLK, DQSW,
    output reg Q
);

    reg [3:0] data_reg;

    always @(posedge ECLK) begin
        if (RST) begin
            Q <= 1'b0;
            data_reg <= 4'b0;
        end
        else if (!DQSW) begin
            data_reg <= {data_reg[2:0], D3};
        end
        else begin
            Q <= ~^data_reg;
            data_reg <= {D3, D2, D1, D0};
        end
    end

endmodule