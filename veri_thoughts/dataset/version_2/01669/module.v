module add_sub_mux (
    input [3:0] a,
    input [3:0] b,
    input mode,
    input [3:0] B,
    input [3:0] C,
    input [3:0] D,
    input [3:0] E,
    input [1:0] SEL,
    input EN,
    output reg [3:0] q
);

    wire [3:0] add_sub_out;
    wire [3:0] mux_out;
    
    add_sub add_sub_inst (
        .a(a),
        .b(b),
        .mode(mode),
        .q(add_sub_out)
    );
    
    mux_4to1 mux_inst (
        .a(add_sub_out),
        .b(B),
        .c(C),
        .d(D),
        .e(E),
        .sel(SEL),
        .en(EN),
        .q(mux_out)
    );
    
    always @(*) begin
        q = mux_out;
    end

endmodule

module add_sub(
    input [3:0] a,
    input [3:0] b,
    input mode,
    output reg [3:0] q
);

    always @(*) begin
        if (mode) begin
            q = a + b;
        end else begin
            q = a - b;
        end
    end

endmodule

module mux_4to1(
    input [3:0] a,
    input [3:0] b,
    input [3:0] c,
    input [3:0] d,
    input [3:0] e,
    input [1:0] sel,
    input en,
    output reg [3:0] q
);

    always @(*) begin
        case (sel)
            2'b00: q = a;
            2'b01: q = b;
            2'b10: q = c;
            2'b11: q = d;
        endcase
        if (!en) begin
            q = e;
        end
    end

endmodule