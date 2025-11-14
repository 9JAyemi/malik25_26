
module counter (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [3:0] count
);

    // State definitions
    localparam [1:0]
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10,
        S3 = 2'b11;

    // State register
    reg [1:0] state;

    always @(posedge clk) begin
        if (reset) begin
            state <= S0;
            count <= 4'b0000;
        end else begin
            case (state)
                S0: begin
                    state <= S1;
                    count <= count + 1;
                end
                S1: begin
                    state <= S2;
                    count <= count + 1;
                end
                S2: begin
                    state <= S3;
                    count <= count + 1;
                end
                S3: begin
                    state <= S0;
                    count <= count + 1;
                end
            endcase
        end
    end

endmodule

module odd_even_detector (
    input [3:0] count,
    output reg odd_even
);

    always @(*)
        odd_even = count[0];

endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [6:0] seg,
    output odd_even
);

    wire [3:0] count;
    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .count(count)
    );

    odd_even_detector odd_even_inst (
        .count(count),
        .odd_even(odd_even)
    );

    always @(count) begin
        case (count)
            4'b0000: seg = 7'b1000000; // 0
            4'b0001: seg = 7'b1111001; // 1
            4'b0010: seg = 7'b0100100; // 2
            4'b0011: seg = 7'b0110000; // 3
            4'b0100: seg = 7'b0011001; // 4
            4'b0101: seg = 7'b0010010; // 5
            4'b0110: seg = 7'b0000010; // 6
            4'b0111: seg = 7'b1111000; // 7
            4'b1000: seg = 7'b0000000; // 8
            4'b1001: seg = 7'b0011000; // 9
            4'b1010: seg = 7'b0001000; // A
            4'b1011: seg = 7'b0000011; // B
            4'b1100: seg = 7'b1000110; // C
            4'b1101: seg = 7'b0100001; // D
            4'b1110: seg = 7'b0000110; // E
            4'b1111: seg = 7'b0001110; // F
        endcase
    end

endmodule
