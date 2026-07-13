module counterB (
    output reg [3:0] cntB_reg, // Registered version of cntA
    input decrementB, // 0=Up-counting, 1=down-counting
    input dual_countB, // Advance counter by 2 steps at a time
    input cntB_en, // Enable counter B
    input clk, // Clock
    input rst // Synchronous reset
);

    // Counter B - tried to write sequential only, but ended up without
    // SystemVerilog.

    always @(posedge clk) begin
        if (rst)
            cntB_reg <= 4'b0000;
        else if (cntB_en) begin
            if (decrementB) begin
                if (dual_countB)
                    cntB_reg <= cntB_reg - 2;
                else
                    cntB_reg <= cntB_reg - 1;
            end
            else begin
                if (dual_countB)
                    cntB_reg <= cntB_reg + 2;
                else
                    cntB_reg <= cntB_reg + 1;
            end
        end
    end // always @

endmodule