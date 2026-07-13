module binary_to_gray (
    input [3:0] BIN,
    output reg [3:0] GRAY
);

always @ (BIN) begin
    GRAY[0] = BIN[0] ^ BIN[1];
    GRAY[1] = BIN[1] ^ BIN[2];
    GRAY[2] = BIN[2] ^ BIN[3];
    GRAY[3] = BIN[3];
end

endmodule