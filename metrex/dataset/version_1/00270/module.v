module binary_gray_updown (
    input clk,
    input rst,
    input en,
    input up,
    input select,
    input [2:0] BIN,
    output reg [2:0] GRAY,
    output reg [3:0] count
);

    wire [2:0] gray_out;
    binary_to_gray_converter gray_converter(.bin(BIN), .gray(gray_out));
    always @ (posedge clk) begin
        if (rst) begin
            count <= 0;
        end else if (en) begin
            if (select) begin
                // Binary-to-Gray conversion mode
                GRAY <= gray_out;
            end else begin
                // Counter mode
                if (up) begin
                    count <= count + 1;
                end else begin
                    count <= count - 1;
                end
                GRAY <= 3'b000;
            end
        end
    end

endmodule

module binary_to_gray_converter (
    input [2:0] bin,
    output reg [2:0] gray
);

    always @* begin
        gray[0] = bin[0] ^ bin[1];
        gray[1] = bin[1] ^ bin[2];
        gray[2] = bin[2];
    end

endmodule