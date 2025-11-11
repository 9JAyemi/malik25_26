
module hard_sync #(
    parameter INIT = 1'b0, // optional initialization value
    parameter IS_CLK_INVERTED = 1'b0, // optional clock inversion
    parameter LATENCY = 2 // latency of 2 or 3 clock cycles
)(
    output reg DOUT,
    input CLK,
    input DIN
);

    reg [2:0] DIN_reg; // register to store input data

    always @(posedge CLK) begin
        if (IS_CLK_INVERTED) begin // invert clock if enabled
            DIN_reg <= {DIN_reg[1:0], ~DIN};
        end else begin
            DIN_reg <= {DIN_reg[1:0], DIN};
        end

        if (LATENCY == 2) begin // synchronize output after 2 clock cycles
            DOUT <= DIN_reg[1];
        end else begin // synchronize output after 3 clock cycles
            DOUT <= DIN_reg[2];
        end
    end

    initial begin
        DIN_reg <= {INIT, INIT, INIT}; // initialize register with INIT value
    end

endmodule