
module bin2gray(
    input [2:0] bin,
    input reset,
    output reg [2:0] gray
);


always @(*) begin
    if (reset) begin
        gray <= 3'b0;
    end
    else begin
        gray[2] = bin[2];
        gray[1] = gray[2] ^ bin[1];
        gray[0] = gray[1] ^ bin[0];
    end
end

endmodule