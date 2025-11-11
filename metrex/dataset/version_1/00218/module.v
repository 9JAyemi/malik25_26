module top_module (
    input clk,
    input reset,
    input signed [3:0] A,
    input signed [3:0] B,
    input A_input,
    input B_input,
    input EN,
    output reg signed [7:0] P_output
);

    wire [3:0] decoder_out;
    wire [7:0] multiplier_out;
    
    decoder_2to4_with_enable decoder_2to4_with_enable_inst (
        .A(A_input),
        .B(B_input),
        .EN(EN),
        .Y(decoder_out)
    );
    
    booth_multiplier booth_multiplier_inst (
        .clk(clk),
        .reset(reset),
        .A(A),
        .B(B),
        .P(multiplier_out)
    );
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            P_output <= 0;
        end else begin
            if (EN) begin
                P_output <= multiplier_out;
            end else begin
                P_output <= 0;
            end
        end
    end
    
endmodule

module decoder_2to4_with_enable (
    input A,
    input B,
    input EN,
    output reg [3:0] Y
);
    
    always @* begin
        case ({A,B,EN})
            3'b000: Y = 4'b0001;
            3'b001: Y = 4'b0010;
            3'b010: Y = 4'b0100;
            3'b011: Y = 4'b1000;
            3'b1xx: Y = 4'b0000;
        endcase
    end
    
endmodule

module booth_multiplier (
    input clk,
    input reset,
    input signed [3:0] A,
    input signed [3:0] B,
    output reg signed [7:0] P
);
    
    reg signed [7:0] P_reg;
    reg signed [3:0] A_reg;
    reg signed [3:0] B_reg;
    reg [2:0] state;
    
    always @* begin
        P = P_reg;
    end
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            P_reg <= 0;
            A_reg <= 0;
            B_reg <= 0;
            state <= 3'b000;
        end else begin
            case (state)
                3'b000: begin
                    if (B[0] == 1) begin
                        P_reg <= -A;
                    end else begin
                        P_reg <= A;
                    end
                    A_reg <= A;
                    B_reg <= B;
                    state <= 3'b001;
                end
                3'b001: begin
                    if (B[0] == 1 && B[1] == 0) begin
                        P_reg <= P_reg - (A_reg << 1);
                    end else if (B[0] == 0 && B[1] == 1) begin
                        P_reg <= P_reg + (A_reg << 1);
                    end
                    A_reg <= A_reg << 1;
                    B_reg <= B >> 1;
                    state <= 3'b010;
                end
                3'b010: begin
                    if (B[0] == 1) begin
                        P_reg <= P_reg - B_reg;
                    end else if (B[0] == 0) begin
                        P_reg <= P_reg + B_reg;
                    end
                    A_reg <= A_reg;
                    B_reg <= B_reg >> 1;
                    state <= 3'b011;
                end
                3'b011: begin
                    state <= 3'b000;
                end
            endcase
        end
    end
    
endmodule