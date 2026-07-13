module priority_mux (
    input [3:0] A, B, C, D,
    input [1:0] S,
    output reg Y, Z
);

always @(*) begin
    case(S)
        2'b00: begin
            if(A) begin
                Y = 1;
                Z = 0;
            end
            else if(B) begin
                Y = 0;
                Z = 1;
            end
            else if(C) begin
                Y = 0;
                Z = 0;
            end
            else if(D) begin
                Y = 0;
                Z = 0;
            end
            else begin
                Y = 0;
                Z = 0;
            end
        end
        2'b01: begin
            if(B) begin
                Y = 0;
                Z = 1;
            end
            else if(A) begin
                Y = 1;
                Z = 0;
            end
            else if(C) begin
                Y = 0;
                Z = 0;
            end
            else if(D) begin
                Y = 0;
                Z = 0;
            end
            else begin
                Y = 0;
                Z = 0;
            end
        end
        2'b10: begin
            if(C) begin
                Y = 0;
                Z = 0;
            end
            else if(A) begin
                Y = 1;
                Z = 0;
            end
            else if(B) begin
                Y = 0;
                Z = 1;
            end
            else if(D) begin
                Y = 0;
                Z = 0;
            end
            else begin
                Y = 0;
                Z = 0;
            end
        end
        2'b11: begin
            if(D) begin
                Y = 0;
                Z = 0;
            end
            else if(A) begin
                Y = 1;
                Z = 0;
            end
            else if(B) begin
                Y = 0;
                Z = 1;
            end
            else if(C) begin
                Y = 0;
                Z = 0;
            end
            else begin
                Y = 0;
                Z = 0;
            end
        end
    endcase
end

endmodule