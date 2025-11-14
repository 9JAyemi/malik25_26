module gray_counter (
    input clk,      // Clock input
    input reset,    // Synchronous active-low reset
    output reg [3:0] gray_count   // 4-bit Gray counter output
);

    reg [3:0] binary_count;

    always @(posedge clk, negedge reset) begin
        if (!reset) begin
            binary_count <= 4'b0000;
        end else begin
            binary_count <= binary_count + 1;
        end
    end

    always @* begin
        case (binary_count)
            4'b0000: gray_count = 4'b0000;
            4'b0001: gray_count = 4'b0001;
            4'b0011: gray_count = 4'b0011;
            4'b0010: gray_count = 4'b0010;
            4'b0110: gray_count = 4'b0110;
            4'b0111: gray_count = 4'b0111;
            4'b0101: gray_count = 4'b0101;
            4'b0100: gray_count = 4'b0100;
            4'b1100: gray_count = 4'b1100;
            4'b1101: gray_count = 4'b1101;
            4'b1111: gray_count = 4'b1111;
            4'b1110: gray_count = 4'b1110;
            4'b1010: gray_count = 4'b1010;
            4'b1011: gray_count = 4'b1011;
            4'b1001: gray_count = 4'b1001;
            4'b1000: gray_count = 4'b1000;
            default: gray_count = 4'b0000;
        endcase
    end

endmodule

module combinatorial_circuit (
    input [7:0] in_hi,      // Upper byte input
    input [7:0] in_lo,      // Lower byte input
    output reg [15:0] out   // 16-bit output
);

    always @* begin
        out = {in_hi, in_lo};
    end

endmodule

module top_module (
    input clk,              // Clock input
    input reset,            // Synchronous active-low reset
    input [7:0] in_hi,      // Upper byte input
    input [7:0] in_lo,      // Lower byte input
    output reg [19:0] out   // 20-bit output
);

    wire [3:0] gray_count;
    wire [15:0] comb_out;

    gray_counter gray_inst (
        .clk(clk),
        .reset(reset),
        .gray_count(gray_count)
    );

    combinatorial_circuit comb_inst (
        .in_hi(in_hi),
        .in_lo(in_lo),
        .out(comb_out)
    );

    always @(posedge clk, negedge reset) begin
        if (!reset) begin
            out <= 20'b00000000000000000000;
        end else begin
            out <= {comb_out, gray_count};
        end
    end

endmodule