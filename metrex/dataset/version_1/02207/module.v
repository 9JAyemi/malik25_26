
module top_module (
    input a, b, c,
    input [7:0] in,
    output reg [2:0] pos,
    output reg w, x, y, z
);

    // Priority Encoder
    wire [7:0] in_inv;
    assign in_inv = ~in;
    wire [2:0] pos_inv;
    priority_encoder pe(
        .in(in_inv),
        .pos(pos_inv)
    );
    
    // Multiplexer
    wire [1:0] sel = pos_inv[1:0];
    mux4to1 mux(
        .a(a),
        .b(b),
        .c(c),
        .d(0),
        .sel(sel)
    );
    
    // Output
    always @(*) begin
        case (pos_inv)
            3'b000: begin
                w <= in[sel];
                x <= 0;
                y <= 0;
                z <= 0;
            end
            3'b001: begin
                w <= 0;
                x <= in[sel];
                y <= 0;
                z <= 0;
            end
            3'b010: begin
                w <= 0;
                x <= 0;
                y <= in[sel];
                z <= 0;
            end
            3'b011: begin
                w <= 0;
                x <= 0;
                y <= 0;
                z <= in[sel];
            end
            default: begin
                w <= 0;
                x <= 0;
                y <= 0;
                z <= 0;
            end
        endcase
    end
    
    // Output Position
    always @(in) begin
        if (in == 8'b00000000) begin
            pos <= 3'b000;
        end else begin
            pos <= pos_inv;
        end
    end
    
endmodule
module mux4to1 (
    input a, b, c, d,
    input [1:0] sel,
    output reg out
);

    always @* begin
        case (sel)
            2'b00: out <= a;
            2'b01: out <= b;
            2'b10: out <= c;
            2'b11: out <= d;
            default: out <= 0;
        endcase
    end
    
endmodule
module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);

    always @* begin
        casez (in)
            8'b00000001: pos <= 3'b000;
            8'b00000011: pos <= 3'b001;
            8'b00000111: pos <= 3'b010;
            8'b00001111: pos <= 3'b011;
            8'b00011111: pos <= 3'b100;
            8'b00111111: pos <= 3'b101;
            8'b01111111: pos <= 3'b110;
            8'b11111111: pos <= 3'b111;
            default: pos <= 3'b000;
        endcase
    end
    
endmodule