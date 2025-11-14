
module opModule (clk, iA, iB, iC, oResult);
    input clk;
    input [3:0] iA;
    input [3:0] iB;
    input iC;
    output [3:0] oResult;

    reg [3:0] oResult_reg; // Declare oResult as a register

    always @(posedge clk) begin
        if (iC == 0) begin
            oResult_reg <= iA & iB;
        end else begin
            oResult_reg <= iA | iB;
        end
    end

    assign oResult = oResult_reg; // Assign the value of oResult_reg to oResult
endmodule
