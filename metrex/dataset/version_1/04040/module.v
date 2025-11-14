
module dly1_17_mod (
    input wire [16:0] i,
    input wire rst,
    input wire clk,
    output wire [16:0] o,
    output wire done
);

    reg [16:0] temp;
    reg done_reg;
    reg done_next;

    assign o = temp;
    assign done = done_reg;

    always @(posedge rst or posedge clk)
    begin
        if (rst)
        begin
            temp <= 0;
            done_reg <= 0;
        end
        else
        begin
            temp <= i;
            done_next <= (temp == i);
            done_reg <= done_next;
        end
    end

endmodule