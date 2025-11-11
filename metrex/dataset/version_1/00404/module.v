
module magnitude_comparator (
    input clk,
    input [3:0] A,
    input [3:0] B,
    output reg out
);

reg [3:0] A_reg, B_reg;
reg [1:0] stage;

always @(posedge clk) begin
    case(stage)
        0: begin
            A_reg <= A;
            B_reg <= B;
            stage <= 1;
        end
        1: begin
            if (|A_reg > |B_reg) begin
                out <= 1;
            end else begin
                out <= 0;
            end
            stage <= 0;
        end
    endcase
end

endmodule