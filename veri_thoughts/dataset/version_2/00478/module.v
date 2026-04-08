
module my_flip_flop (
    input clk,
    input d,
    input rst,
    output q
);

    reg q_reg;

    always @(posedge clk) begin
        if (rst) begin
            q_reg <= 1'b0;
        end else begin
            q_reg <= d;
        end
    end

    assign q = q_reg;

endmodule
