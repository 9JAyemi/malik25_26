module ZigbeeReceiver #(
    parameter n = 8 // Number of output data bits
)(
    input wire carrier,
    input wire modulated,
    input wire en,
    input wire clk,
    output reg [n-1:0] out
);

    always @(posedge clk) begin
        if (en && carrier) begin
            out <= {n{modulated}}; // Placeholder for actual demodulation logic
        end
        else begin
            out <= 0;
        end
    end

endmodule
