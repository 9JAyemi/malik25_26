
module muxMUL (ia, ib, o);

    input wire [3:0] ia, ib;
    output reg [7:0] o;

    wire [7:0] iaR, iaRA, o0, o1, o1R;

    assign iaR = ia << 1;
    assign iaRA = iaR + ia;

    mux mux0 (.in0(8'b0), .in1({4'b0, ia}), .in2(iaR), .in3(iaRA), .sel(ib[1:0]), .out(o0));
    mux mux1 (.in0(8'b0), .in1({4'b0, ia}), .in2(iaR), .in3(iaRA), .sel(ib[3:2]), .out(o1));

    assign o1R = o1 << 2;
    always @(*) begin
        o = o0 + o1R;
    end

endmodule
module mux (in0, in1, in2, in3, sel, out);

    input wire [7:0] in0, in1, in2, in3;
    input wire [1:0] sel;
    output reg [7:0] out;

    always @(*) begin
        case (sel)
            2'b00: out <= in0;
            2'b01: out <= in1;
            2'b10: out <= in2;
            2'b11: out <= in3;
        endcase
    end

endmodule