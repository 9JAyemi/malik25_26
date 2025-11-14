
module top_module (
    input [15:0] a,
    input [15:0] b,
    output lt,
    output eq,
    output gt,
    output [6:0] seg_a,
    output [6:0] seg_b
);

    wire [3:0] bcd_a;
    wire [3:0] bcd_b;
    bcd_to_7seg bcd_a_decoder(bcd_a, seg_a);
    bcd_to_7seg bcd_b_decoder(bcd_b, seg_b);
    comparator_16bit comparator(a, b, lt, eq, gt);

    assign {bcd_a, bcd_b} = {a,b};

endmodule

module bcd_to_7seg (
    input [3:0] BCD,
    output [6:0] SEG
);
    reg [6:0] SEG;
    always @*
    begin
        case (BCD)
            4'b0000: SEG = 7'b1000000; // 0
            4'b0001: SEG = 7'b1111001; // 1
            4'b0010: SEG = 7'b0100100; // 2
            4'b0011: SEG = 7'b0110000; // 3
            4'b0100: SEG = 7'b0011001; // 4
            4'b0101: SEG = 7'b0010010; // 5
            4'b0110: SEG = 7'b0000010; // 6
            4'b0111: SEG = 7'b1111000; // 7
            4'b1000: SEG = 7'b0000000; // 8
            4'b1001: SEG = 7'b0010000; // 9
            default: SEG = 7'b1111111; // Invalid input
        endcase
    end

endmodule

module comparator_16bit (
    input [15:0] a,
    input [15:0] b,
    output lt,
    output eq,
    output gt
);
    assign lt = (a < b);
    assign eq = (a == b);
    assign gt = (a > b);
endmodule
