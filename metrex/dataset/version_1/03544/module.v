module Test (
    input clk, 
    input rstn, 
    input clken, 
    input [3:0] in, 
    output [3:0] ff_out, 
    output [3:0] fg_out, 
    output [3:0] fh_out
);

    reg [3:0] in_reg;
    reg [3:0] ff_out_reg;
    reg [3:0] fg_out_reg;
    reg [3:0] fh_out_reg;

    always @(posedge clk) begin
        if (rstn == 0) begin
            in_reg <= 0;
            ff_out_reg <= 0;
            fg_out_reg <= 0;
            fh_out_reg <= 0;
        end
        else if (clken == 1) begin
            in_reg <= in;
            ff_out_reg <= in_reg * 2;
            fg_out_reg <= in_reg * 3;
            fh_out_reg <= in_reg * 4;
        end
    end

    assign ff_out = ff_out_reg;
    assign fg_out = fg_out_reg;
    assign fh_out = fh_out_reg;

endmodule