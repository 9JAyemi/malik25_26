module signed_gte_4bit (
    input signed [3:0] A,
    input signed [3:0] B,
    input clk,
    output reg GTE
);

reg signed [3:0] A_reg, B_reg;
reg [1:0] stage;

always @(posedge clk) begin
    case(stage)
        2'b00: begin
            A_reg <= A;
            B_reg <= B;
            stage <= 2'b01;
        end
        2'b01: begin
            if (A_reg >= B_reg)
                GTE <= 1;
            else
                GTE <= 0;
            stage <= 2'b00;
        end
    endcase;
end

endmodule