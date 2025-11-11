
module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input [2:0] sel,
    output [3:0] out,
    output parity,
    output overflow
);

    wire [7:0] sum;
    wire add_overflow;
    add_overflow_detection adder(a, b, sum, add_overflow);

    wire [3:0] data0;
    wire [3:0] data1;
    wire [3:0] data2;
    wire [3:0] data3;
    wire [3:0] data4;
    wire [3:0] data5;

    assign data0 = a[3:0];
    assign data1 = b[3:0];
    assign data2 = sum[3:0];
    assign data3 = 4'b0;
    assign data4 = 4'b0;
    assign data5 = 4'b0;

    reg [3:0] out_reg;
    reg overflow_reg;

    always @(posedge clk) begin
        if (reset) begin
            out_reg <= 4'b0;
            overflow_reg <= 1'b0;
        end else begin
            case (sel)
                3'b000: begin
                    out_reg <= data0;
                end
                3'b001: begin
                    out_reg <= data1;
                end
                3'b010: begin
                    out_reg <= data2;
                    overflow_reg <= add_overflow;
                end
                default: begin
                    out_reg <= 4'b0;
                    overflow_reg <= 1'b0;
                end
            endcase
        end
    end

    mux mux_parity(sel, data0, data1, data2, data3, data4, data5, parity);

    assign out = out_reg;
    assign overflow = overflow_reg;

endmodule

module add_overflow_detection (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);
    assign s = a + b;
    assign overflow = ((a[7] == b[7]) && (s[7] != a[7]));
endmodule

module mux (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg parity
);

    always @(*) begin
        case (sel)
            3'b000: parity = ^data0;
            3'b001: parity = ^data1;
            3'b010: parity = ^data2;
            3'b011: parity = ^data3;
            3'b100: parity = ^data4;
            3'b101: parity = ^data5;
            default: parity = 1'b0;
        endcase
    end

endmodule
