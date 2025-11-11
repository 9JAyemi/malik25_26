module mag_comparator_4bit (
    input [3:0] A,
    input [3:0] B,
    output reg LT,
    input clk 
);

reg [3:0] A_reg, B_reg;
reg [2:0] stage;

// Added clock in the sensitivity list
always @(posedge clk) begin
    case(stage)
        0: begin
            A_reg <= A;
            B_reg <= B;
            stage <= 1;
        end
        1: begin
            if(A_reg < B_reg) begin
                LT <= 1'b1; // Fixed the assignment to LT
            end else begin
                LT <= 1'b0; // Fixed the assignment to LT
            end
            stage <= 0;
        end
    endcase
end

endmodule