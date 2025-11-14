
module top_module (
    input signed [3:0] A,
    input signed [3:0] B,
    input sel,
    output reg C
);

    wire signed [3:0] mux_output;
    wire signed [0:0] mag_comp_output;

    mux_2to1 mux (
        .in({A, B}),
        .sel(sel),
        .out(mux_output)
    );

    signed_mag_comp mag_comp (
        .A(A),
        .B(B),
        .C(mag_comp_output)
    );

    always @(*) begin
        if (sel == 0) begin
            if (mag_comp_output == 1'b1) begin
                C <= 1'b1;
            end else if (A > B) begin
                C <= 1'b0;
            end else begin
                C <= 1'b0;
            end
        end else begin
            C <= mux_output;
        end
    end

endmodule

module mux_2to1 (
    input [7:0] in,
    input sel,
    output reg [3:0] out
);

    always @(in, sel) begin
        case (sel)
            1'b0: out <= in[3:0];
            1'b1: out <= in[7:4];
            default: out <= in[3:0];
        endcase
    end

endmodule

module signed_mag_comp (
    input signed [3:0] A,
    input signed [3:0] B,
    output reg [0:0] C
);

    always @(A, B) begin
        if (A == B) begin
            C <= 1'b1;
        end else if (A > B) begin
            C <= 1'b0;
        end else begin
            C <= 1'b0;
        end
    end

endmodule
