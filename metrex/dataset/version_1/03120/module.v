
module dff_async_reset_set_enable(
    input D,
    input CLK,
    input RESET,
    input SET,
    input EN,
    output reg Q,
    output reg QBAR
);

    reg R = 0;

    always @(posedge CLK) begin
        if (RESET) begin
            R <= 1'b1;
            Q <= 1'b0;
            QBAR <= 1'b1;
        end 
        else if (SET) begin
            R <= 1'b1;
            Q <= 1'b1;
            QBAR <= 1'b0;
        end 
        else if (EN & ~R) begin
            Q <= D;
            QBAR <= ~D;
        end
        R <= 0;
    end

endmodule