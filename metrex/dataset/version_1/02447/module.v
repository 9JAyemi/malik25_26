module booth_shift_reg (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input load,
    input shift_left,
    input shift_right,
    input select,
    output [7:0] P,
    output [7:0] P_shifted
);

reg [7:0] P_reg;
reg [3:0] A_reg;
reg [3:0] B_reg;
reg [2:0] count;
reg [3:0] B_shifted;
reg [1:0] shift_count;

always @(posedge clk) begin
    if (reset) begin
        P_reg <= 8'b0;
        A_reg <= 4'b0;
        B_reg <= 4'b0;
        count <= 3'b0;
        B_shifted <= 4'b0;
        shift_count <= 2'b0;
    end else begin
        if (load) begin
            P_reg <= 8'b0;
            A_reg <= A;
            B_reg <= B;
            count <= 3'b0;
            B_shifted <= {B[3], B};
            shift_count <= 2'b0;
        end else begin
            case (count)
                3'b000: begin
                    if (B_reg[0] == 1) begin
                        P_reg <= P_reg + (A_reg << 4);
                    end
                    B_shifted <= {B[3], B};
                    shift_count <= 2'b0;
                end
                3'b001: begin
                    if (B_reg[0] == 0 && B_shifted[0] == 1) begin
                        P_reg <= P_reg - (A_reg << 4);
                    end
                    B_shifted <= {B_shifted[3], B_shifted};
                    shift_count <= 2'b1;
                end
                3'b010: begin
                    if (B_reg[0] == 1) begin
                        P_reg <= P_reg + (A_reg << 3);
                    end
                    B_shifted <= {B[3], B};
                    shift_count <= 2'b0;
                end
                3'b011: begin
                    if (B_reg[0] == 0 && B_shifted[0] == 1) begin
                        P_reg <= P_reg - (A_reg << 3);
                    end
                    B_shifted <= {B_shifted[3], B_shifted};
                    shift_count <= 2'b1;
                end
                3'b100: begin
                    if (B_reg[0] == 1) begin
                        P_reg <= P_reg + (A_reg << 2);
                    end
                    B_shifted <= {B[3], B};
                    shift_count <= 2'b0;
                end
                3'b101: begin
                    if (B_reg[0] == 0 && B_shifted[0] == 1) begin
                        P_reg <= P_reg - (A_reg << 2);
                    end
                    B_shifted <= {B_shifted[3], B_shifted};
                    shift_count <= 2'b1;
                end
                3'b110: begin
                    if (B_reg[0] == 1) begin
                        P_reg <= P_reg + (A_reg << 1);
                    end
                    B_shifted <= {B[3], B};
                    shift_count <= 2'b0;
                end
                3'b111: begin
                    if (B_reg[0] == 0 && B_shifted[0] == 1) begin
                        P_reg <= P_reg - (A_reg << 1);
                    end
                    B_shifted <= {B_shifted[3], B_shifted};
                    shift_count <= 2'b1;
                end
            endcase
            count <= count + 1;
        end
    end
end

assign P = select ? P_reg : {P_reg[6:0], 1'b0};
assign P_shifted = select ? {P_reg[6:0], 1'b0} : {P_reg[5:0], 2'b0};

endmodule