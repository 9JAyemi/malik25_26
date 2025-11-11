
module seg7 (
    input  wire         clk,
    input  wire         reset,
    input  wire  [15:0] value,
    output reg   [6:0]  seg,
    output reg          dp,
    output reg   [3:0]  an
);


    localparam COUNTER_WIDTH = 18;

    reg [COUNTER_WIDTH-1:0] counter;
    reg counter_msb_d1;
    wire counter_edge;
    reg [1:0] digit;
    wire [6:0] seg0, seg1, seg2, seg3;

    always @(posedge clk) begin
        if (reset == 1'b1) begin
            counter <= {COUNTER_WIDTH{1'b0}};
            counter_msb_d1 <= 1'b0;
        end else begin
            counter <= counter + 1'b1;
            counter_msb_d1 <= counter[COUNTER_WIDTH-1];
        end
    end

    assign counter_edge = ~counter_msb_d1 & counter[COUNTER_WIDTH-1];

    always @(posedge clk) begin
        if (reset == 1'b1) begin
            seg <= 7'b1111111;
            dp  <= 1'b1;
            an  <= 4'b1111;
            digit <= 2'b0;
        end else begin
            if (counter_edge == 1'b1) begin
                digit <= digit + 1'b1;
                case (digit)
                2'b00: begin
                    an  <= 4'b1110;
                    seg <= seg0;
                end
                2'b01: begin
                    an  <= 4'b1101;
                    seg <= seg1;
                end
                2'b10: begin
                    an  <= 4'b1011;
                    seg <= seg2;
                end
                2'b11: begin
                    an  <= 4'b0111;
                    seg <= seg3;
                end
                endcase
            end
        end
    end

    val2seg u_val2seg0 (.value(value[3:0]),   .seg(seg0));
    val2seg u_val2seg1 (.value(value[7:4]),   .seg(seg1));
    val2seg u_val2seg2 (.value(value[11:8]),  .seg(seg2));
    val2seg u_val2seg3 (.value(value[15:12]), .seg(seg3));

endmodule


module val2seg (
    input  wire  [3:0] value,
    output reg   [6:0] seg
);

    localparam CHAR_N        = 7'b1111111;
    localparam CHAR_0        = 7'b1000000;
    localparam CHAR_1        = 7'b1111001;
    localparam CHAR_2        = 7'b0100100;
    localparam CHAR_3        = 7'b0110000;
    localparam CHAR_4        = 7'b0011001;
    localparam CHAR_5        = 7'b0010010;
    localparam CHAR_6        = 7'b0000010;
    localparam CHAR_7        = 7'b1111000;
    localparam CHAR_8        = 7'b0000000;
    localparam CHAR_9        = 7'b0010000;
    localparam CHAR_A        = 7'b0001000;
    localparam CHAR_B        = 7'b0000011;
    localparam CHAR_C        = 7'b1000110;
    localparam CHAR_D        = 7'b0100001;
    localparam CHAR_E        = 7'b0000110;
    localparam CHAR_F        = 7'b0001110;

    always @(*) begin
        case (value)
        4'h0: seg <= CHAR_0;
        4'h1: seg <= CHAR_1;
        4'h2: seg <= CHAR_2;
        4'h3: seg <= CHAR_3;
        4'h4: seg <= CHAR_4;
        4'h5: seg <= CHAR_5;
        4'h6: seg <= CHAR_6;
        4'h7: seg <= CHAR_7;
        4'h8: seg <= CHAR_8;
        4'h9: seg <= CHAR_9;
        4'hA: seg <= CHAR_A;
        4'hB: seg <= CHAR_B;
        4'hC: seg <= CHAR_C;
        4'hD: seg <= CHAR_D;
        4'hE: seg <= CHAR_E;
        4'hF: seg <= CHAR_F;
        default: seg <= CHAR_N;
        endcase
    end

endmodule


