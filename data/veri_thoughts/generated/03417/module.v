
module top_module (
    input signed [3:0] A,
    input signed [3:0] B,
    input EN,
    output [15:0] Q,
    output C
);

    wire [3:0] abs_A, abs_B;
    wire eq, gt, lt;
    reg [1:0] sel;
    
    signed_mag_comp comp(.A(A), .B(B), .eq(eq), .gt(gt), .lt(lt), .abs_A(abs_A), .abs_B(abs_B));
    decoder dec(.SEL(sel), .EN(EN), .Q(Q));
    
    assign C = eq;
    
    always @(*) begin
        if (EN) begin
            if (eq) begin
                sel = 2'b00;
            end else if (gt) begin
                sel = 2'b01;
            end else if (lt) begin
                sel = 2'b10;
            end
        end else begin
            sel = 2'b11;
        end
    end
    
endmodule

module signed_mag_comp (
    input signed [3:0] A,
    input signed [3:0] B,
    output eq,
    output gt,
    output lt,
    output [3:0] abs_A,
    output [3:0] abs_B
);
    
    assign eq = (A == B);
    assign gt = (A > B);
    assign lt = (A < B);
    assign abs_A = (A < 0) ? (~A + 1) : A;
    assign abs_B = (B < 0) ? (~B + 1) : B;
    
endmodule

module decoder (
    input [1:0] SEL,
    input EN,
    output reg [15:0] Q
);
    
    always @(SEL or EN) begin
        if (!EN) begin
            Q = 16'b0000000000000000;
        end else begin
            case (SEL)
                2'b00: Q = 16'b0000000000000001;
                2'b01: Q = 16'b0000000000000010;
                2'b10: Q = 16'b0000000000000100;
                2'b11: Q = 16'b0000000000001000;
                default: Q = 16'b0000000000000000;
            endcase
        end
    end
    
endmodule
