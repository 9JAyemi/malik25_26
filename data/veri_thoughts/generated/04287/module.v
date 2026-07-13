module up_counter(clk, rst, count, overflow);
    input clk, rst;
    output [3:0] count;
    output overflow;
    reg [3:0] count;

    always @(posedge clk, posedge rst)
    begin
        if (rst)
            count <= 4'b0;
        else if (count == 4'hf)
            count <= 4'b0;
        else
            count <= count + 1;
    end

    assign overflow = (count == 4'hf);
endmodule