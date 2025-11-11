
module uart_tx_8n1 (
    input clk,
    input [7:0] txbyte,
    input senddata,
    output txdone,
    output reg tx
);

reg [3:0] state;
reg [7:0] data;
reg startbit;
reg [2:0] bitcount;

assign txdone = (state == 3'b100);

always @(posedge clk) begin
    case (state)
        3'b000: begin // idle
            tx <= 1'b1;
            if (senddata) begin
                state <= 3'b001; // start bit
                data <= txbyte;
                startbit <= 1'b0;
                bitcount <= 3'b000;
            end
        end
        3'b001: begin // start bit
            tx <= 1'b0;
            startbit <= 1'b1;
            state <= 3'b010; // data bits
        end
        3'b010: begin // data bits
            tx <= data[0];
            data <= {data[6:0], 1'b0};
            bitcount <= bitcount + 1;
            if (bitcount == 3'b111) begin
                state <= 3'b011; // stop bit
            end
        end
        3'b011: begin // stop bit
            tx <= 1'b1;
            state <= 3'b100; // done
        end
        default: begin // done
            tx <= 1'b1;
        end
    endcase
end

endmodule