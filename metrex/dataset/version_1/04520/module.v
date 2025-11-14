module priority_mux_addsub (
    input [3:0] A, B, C, D, // Four 4-bit inputs
    input [1:0] S, // Select input to choose between the inputs
    input SUB, // 1-bit input for subtraction
    output reg [3:0] out // 4-bit output from the final module
);

    // Priority encoder-based multiplexer
    wire [1:0] sel;
    priority_encoder pe(.in(S), .out(sel));
    wire [3:0] mux_out;
    mux_4to1 mux(.in0(A), .in1(B), .in2(C), .in3(D), .sel(sel), .out(mux_out));

    // 4-bit adder-subtractor
    wire [3:0] addsub_out;
    addsub_4bit addsub(.A(A), .B(mux_out), .SUB(SUB), .out(addsub_out));

    // Final module to get the output
    always @* begin
        out = addsub_out;
    end

endmodule

module priority_encoder (
    input [1:0] in,
    output reg [1:0] out
);

    always @* begin
        if (in == 2'b00) begin
            out = 2'b00;
        end else if (in == 2'b01) begin
            out = 2'b01;
        end else if (in == 2'b10) begin
            out = 2'b10;
        end else begin
            out = 2'b11;
        end
    end

endmodule

module mux_4to1 (
    input [3:0] in0, in1, in2, in3,
    input [1:0] sel,
    output reg [3:0] out
);

    always @* begin
        case(sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            2'b11: out = in3;
        endcase
    end

endmodule

module addsub_4bit (
    input [3:0] A, B,
    input SUB,
    output reg [3:0] out
);

    always @* begin
        if (SUB) begin
            out = A - B;
        end else begin
            out = A + B;
        end
    end

endmodule