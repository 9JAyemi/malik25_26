module counter_4bit_sync_reset (
    input wire CK,
    input wire RST,
    output reg [3:0] Q
);

    always @(posedge CK) begin
        if(RST) begin
            Q <= 4'b0;
        end
        else begin
            Q <= Q + 1;
        end
    end

endmodule